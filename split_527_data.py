from collections import defaultdict
import os
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from rapidfuzz import process, fuzz
from tqdm import tqdm
import time
import queue

# Constants
THRESHOLD = 60  # Fuzzy match score threshold

# Define headers for each record type
headers = {
    "H": ["record_type", "file_date", "version", "flag"],
    "1": ["record_type", "form_id_number", "initial_or_amended", "organization_type", "filing_date", "amended_date",
          "ein", "organization_name", "address_line_1", "address_line_2", "city", "state", "zip_code", "contact_email",
          "contact_phone", "contact_name", "custodian_address_line_1", "custodian_address_line_2", "custodian_city",
          "custodian_state", "custodian_zip_code", "director_1_name", "director_1_address_line_1", "director_1_address_line_2",
          "director_1_city", "director_1_state", "director_1_zip_code", "related_entity_1_name", "related_entity_1_ein",
          "related_entity_1_city", "related_entity_1_state", "related_entity_1_zip_code", "exemption_type", "purpose",
          "date_organized", "date_of_initial_filing", "amended_reason", "qualified_status", "lobbying_expenditures",
          "election_participation", "fundraising_method", "bank_name", "bank_city", "bank_state", "bank_zip_code"],
    "D": ["record_type", "form_id_number", "record_id", "organization_name", "ein", "candidate_name", "candidate_role",
          "address_line_1", "address_line_2", "city", "state", "zip_code", "additional_detail"],
    "R": ["record_type", "form_id_number", "record_id", "organization_name", "ein", "related_name", "relationship_type",
          "related_address_line_1", "related_address_line_2", "related_city", "related_state", "related_zip_code",
          "additional_related_info"],
    "Buff": ["record_type", "form_id_number", "field_3", "field_4", "state_code"],
    "2": ["record_type", "form_id_number", "report_id", "period_begin_date", "period_end_date", "initial_or_amended",
          "filing_date", "address_line_1", "city", "state", "organization_name", "ein", "address_line_2", "zip_code",
          "contact_phone", "contact_email", "date_organized", "contact_name", "contact_address_line_1", "contact_address_line_2",
          "contact_city", "contact_state", "contact_zip_code", "custodian_name", "custodian_address_line_1", "custodian_address_line_2",
          "custodian_city", "custodian_state", "custodian_zip_code", "bank_address_line_1", "bank_address_line_2", "bank_city",
          "bank_state", "bank_zip_code", "schedule_a_indicator", "total_contributions", "total_expenditures", "itemized_contributions",
          "itemized_expenditures", "unitemized_contributions", "cash_on_hand_beginning", "cash_on_hand_end", "contribution_count",
          "expenditure_count", "report_type", "due_date", "amended_reason", "total_receipts"],
    "A": ["record_type", "form_id_number", "schedule_id_number", "organization_name", "organization_ein", "contributor_name",
          "contributor_address_line_1", "contributor_address_line_2", "contributor_city", "contributor_state", "contributor_zip_code",
          "contributor_zip_ext", "contributor_employer", "contribution_amount", "contributor_occupation", "agg_contribution_ytd",
          "contribution_date"],
    "B": ["record_type", "form_id_number", "schedule_id_number", "organization_name", "organization_ein", "recipient_name",
          "recipient_address_line_1", "recipient_address_line_2", "recipient_city", "recipient_state", "recipient_zip_code",
          "recipient_zip_ext", "recipient_employer", "expenditure_amount", "recipient_occupation", "expenditure_date",
          "expenditure_purpose", "fuzzy_match_score"],
    "F": ["record_type", "file_date", "version"]
}

# Keywords for identifying transfers
transfer_keywords = ["contribution", "donation", "transfer", "political contribution"]

# Initialize statistics with lock for thread safety
stats = {
    "total_contributions": 0,
    "contribution_count": 0,
    "total_expenditures": 0,
    "expenditure_count": 0,
    "total_pac_to_pac": 0,
    "pac_to_pac_count": 0,
    "expenditure_by_purpose": defaultdict(float),
    "expenditure_count_by_purpose": defaultdict(int),
    "exceptions": {"A": 0, "B": 0}
}
stats_lock = threading.Lock()

# Cache and histogram
fuzzy_cache = {}
histogram = defaultdict(int)
histogram_lock = threading.Lock()

# Queue for batched 'B' records
b_record_queue = queue.Queue(maxsize=1000)
write_lock = threading.Lock()
writer_should_stop = False

# Open output files and write headers
output_files = {}
for record_type in headers:
    file_name = f"{record_type}_records.txt"
    output_files[record_type] = open(file_name, "w")
    output_files[record_type].write("|".join(headers[record_type]) + "\n")

# Open exception log file
exception_log = open("exception_log.txt", "w")
exception_log.write("Exception Log for Non-Numeric Amount Values\n\n")

# Input file
input_file = "FullDataFile.txt"

# First Pass: Collect PAC names with progress bar
pac_names = set()
start_time = time.time()
print(f"Starting First Pass at {time.strftime('%H:%M:%S')}")
with open(input_file, "r") as infile:
    total_lines = sum(1 for _ in infile)
    infile.seek(0)
    for line in tqdm(infile, total=total_lines, desc="First Pass: Collecting PAC Names"):
        fields = line.strip().split("|")
        if fields and fields[0] == "1" and len(fields) > 7:
            organization_name = fields[7].lower()
            pac_names.add(organization_name)
print(f"First Pass completed at {time.strftime('%H:%M:%S')}, took {time.time() - start_time:.2f} seconds")

# Function to process 'B' records
def process_b_record(line):
    fields = line.strip().split("|")
    if len(fields) < 14:  # Minimum fields for 'B' records
        return

    # Adjust fields to match header
    expected_fields = len(headers["B"])
    if len(fields) < expected_fields:
        fields += [""] * (expected_fields - len(fields))
    elif len(fields) > expected_fields:
        fields = fields[:expected_fields]

    recipient_name = fields[5].lower() if len(fields) > 5 else ""
    purpose = fields[16].lower() if len(fields) > 16 else ""
    amount_str = fields[13] if len(fields) > 13 else ""

    try:
        amount = float(amount_str or 0) if amount_str else 0
        with stats_lock:
            stats["total_expenditures"] += amount
            stats["expenditure_count"] += 1
            stats["expenditure_by_purpose"][purpose] += amount
            stats["expenditure_count_by_purpose"][purpose] += 1

        if recipient_name:
            if recipient_name in fuzzy_cache:
                match, score = fuzzy_cache[recipient_name]
            else:
                result = process.extractOne(recipient_name, pac_names, scorer=fuzz.token_sort_ratio)
                if result:
                    match, score, _ = result
                else:
                    match, score = None, 0
                fuzzy_cache[recipient_name] = (match, score)

            fields[-1] = str(score)  # Add fuzzy match score
            with histogram_lock:
                bin_key = (score // 10 * 10)
                histogram[bin_key] += 1
            if match and score >= THRESHOLD and any(keyword in purpose for keyword in transfer_keywords):
                with stats_lock:
                    stats["total_pac_to_pac"] += amount
                    stats["pac_to_pac_count"] += 1

    except (ValueError, TypeError):
        with stats_lock:
            stats["exceptions"]["B"] += 1
        exception_log.write(f"Record B Exception (Amount: {amount_str}): {line}\n")

    # Add to queue for batched writing
    b_record_queue.put(fields)

# Function to write batched 'B' records
def write_b_records():
    batch = []
    while not writer_should_stop or not b_record_queue.empty():
        try:
            item = b_record_queue.get(timeout=1)
            if item is None:  # Sentinel to stop
                break
            batch.append(item)
            if len(batch) >= 1000:
                with write_lock:
                    for fields in batch:
                        output_files["B"].write("|".join(fields) + "\n")
                batch = []
        except queue.Empty:
            if batch:
                with write_lock:
                    for fields in batch:
                        output_files["B"].write("|".join(fields) + "\n")
                batch = []
    # Final flush
    if batch:
        with write_lock:
            for fields in batch:
                output_files["B"].write("|".join(fields) + "\n")

# Second Pass: Process all records with multithreading
start_time = time.time()
print(f"Starting Second Pass at {time.strftime('%H:%M:%S')}")
writer_thread = threading.Thread(target=write_b_records)
writer_thread.start()
with ThreadPoolExecutor(max_workers=8) as executor:
    futures = []
    with open(input_file, "r") as infile:
        total_lines = sum(1 for _ in infile)
        infile.seek(0)
        processed_lines = 0
        for line in tqdm(infile, total=total_lines, desc="Second Pass: Processing Records"):
            fields = line.strip().split("|")
            if not fields or not fields[0]:
                processed_lines += 1
                continue
            record_type = fields[0]
            if record_type in output_files:
                if record_type == "A":
                    amount_str = fields[13] if len(fields) > 13 else ""
                    try:
                        amount = float(amount_str) if amount_str else 0
                        with stats_lock:
                            stats["total_contributions"] += amount
                            stats["contribution_count"] += 1
                    except (ValueError, TypeError):
                        with stats_lock:
                            stats["exceptions"]["A"] += 1
                        exception_log.write(f"Record A Exception (Amount: {amount_str}): {line}\n")
                    output_files[record_type].write(line)
                    processed_lines += 1
                elif record_type == "B":
                    future = executor.submit(process_b_record, line)
                    futures.append(future)
                    processed_lines += 1
                else:
                    output_files[record_type].write(line)
                    processed_lines += 1
            else:
                processed_lines += 1

    # Wait for all 'B' record tasks to complete
    wait_start = time.time()
    print(f"Starting thread wait at {time.strftime('%H:%M:%S')}")
    for future in as_completed(futures):
        try:
            future.result(timeout=30)
        except Exception as e:
            print(f"Thread error or timeout at {time.strftime('%H:%M:%S')}: {e}")
    print(f"Thread wait completed at {time.strftime('%H:%M:%S')}, took {time.time() - wait_start:.2f} seconds")

    # Signal writer to finish and wait
    writer_should_stop = True
    writer_thread.join()
    print(f"Writer thread completed at {time.strftime('%H:%M:%S')}")

print(f"Second Pass completed at {time.strftime('%H:%M:%S')}, took {time.time() - start_time:.2f} seconds")

# Close all output files and exception log
close_start = time.time()
print(f"Starting file close at {time.strftime('%H:%M:%S')}")
for file in output_files.values():
    file.close()
exception_log.close()
print(f"File close completed at {time.strftime('%H:%M:%S')}, took {time.time() - close_start:.2f} seconds")

# Compute top-5 and bottom-5 purposes by absolute value
stats_start = time.time()
print(f"Starting stats computation at {time.strftime('%H:%M:%S')}")
sorted_purposes = sorted(stats["expenditure_by_purpose"].items(), key=lambda x: abs(x[1]), reverse=True)
top_5 = sorted_purposes[:5]
bottom_5 = sorted_purposes[-5:] if len(sorted_purposes) >= 5 else sorted_purposes[:5]

# Output statistics in Markdown
print("\n# IRS 527 Data Statistics\n")

print("## Contributions\n")
print(f"- **Total Contributions**: ${stats['total_contributions']:,.2f}")
print(f"- **Number of Contributions**: {stats['contribution_count']:,}")
print(f"- **Contribution Exceptions**: {stats['exceptions']['A']:,}")

print("\n## Expenditures\n")
print(f"- **Total Expenditures**: ${stats['total_expenditures']:,.2f}")
print(f"- **Number of Expenditures**: {stats['expenditure_count']:,}")
print(f"- **Expenditure Exceptions**: {stats['exceptions']['B']:,}")

print("\n## PAC-to-PAC Transfers (Approximated)\n")
print(f"- **Total PAC-to-PAC Transfers**: ${stats['total_pac_to_pac']:,.2f} (based on fuzzy matching with score >= {THRESHOLD} and purpose keywords)")
print(f"- **Number of PAC-to-PAC Transfers**: {stats['pac_to_pac_count']:,}")

print("\n## Top-5 Purposes by Absolute Expenditure\n")
print("| Purpose | Total Expenditure | Count | Average Expenditure |")
print("|---------|-------------------|-------|--------------------|")
for purpose, total in top_5:
    count = stats["expenditure_count_by_purpose"][purpose]
    avg = abs(total) / count if count > 0 else 0
    print(f"| {purpose} | ${abs(total):,.2f} | {count:,} | ${avg:,.2f} |")

print("\n## Bottom-5 Purposes by Absolute Expenditure\n")
print("| Purpose | Total Expenditure | Count | Average Expenditure |")
print("|---------|-------------------|-------|--------------------|")
for purpose, total in bottom_5:
    count = stats["expenditure_count_by_purpose"][purpose]
    avg = abs(total) / count if count > 0 else 0
    print(f"| {purpose} | ${abs(total):,.2f} | {count:,} | ${avg:,.2f} |")

print("\n## Fuzzy Match Score Histogram\n")
print("| Score Range | Count |")
print("|-------------|-------|")
for bin_key in range(0, 101, 10):
    count = histogram[bin_key]
    range_str = f"{bin_key}-{min(bin_key + 9, 100)}" if bin_key < 100 else "100"
    print(f"| {range_str} | {count} |")

print(f"Stats computation completed at {time.strftime('%H:%M:%S')}, took {time.time() - stats_start:.2f} seconds")
print(f"Total execution time: {time.time() - start_time:.2f} seconds")
print("\nProcessing complete. Output files created for each record type.")
print("Exception log created: exception_log.txt")