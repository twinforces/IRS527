from collections import defaultdict
import os
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from rapidfuzz import process, fuzz
from tqdm import tqdm

# Define headers for each record type based on IRS 527 documentation
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
          "expenditure_purpose", "fuzzy_match_score"],  # Added new column
    "F": ["record_type", "file_date", "version"]
}

# Keywords for identifying transfers in expenditure purpose
transfer_keywords = ["contribution", "donation", "transfer", "political contribution"]

# Initialize statistics
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

# Cache for fuzzy matching results
fuzzy_cache = {}

# Histogram for fuzzy match scores
histogram = defaultdict(int)
histogram_lock = threading.Lock()

# Lock for writing to 'B' output file
b_write_lock = threading.Lock()

# Open output files and write headers
output_files = {}
for record_type in headers:
    file_name = f"{record_type}_records.txt"
    output_files[record_type] = open(file_name, "w")
    output_files[record_type].write("|".join(headers[record_type]) + "\n")

# Open exception log file
exception_log = open("exception_log.txt", "w")
exception_log.write("Exception Log for Non-Numeric Amount Values\n\n")

# Specify the input file
input_file = "FullDataFile.txt"  # Fixed file name without leading space

# First Pass: Collect PAC names from '1' records with progress bar
pac_names = set()
with open(input_file, "r") as infile:
    # Count total lines for progress bar (optional, can be omitted if file size is unknown)
    total_lines = sum(1 for _ in infile)
    infile.seek(0)
    for line in tqdm(infile, total=total_lines, desc="First Pass: Collecting PAC Names"):
        fields = line.strip().split("|")
        if fields and fields[0] == "1" and len(fields) > 7:
            organization_name = fields[7].lower()  # Organization name at index 7
            pac_names.add(organization_name)

# Function to process 'B' records with fuzzy matching
def process_b_record(line):
    fields = line.strip().split("|")
    if len(fields) < 14:
        return  # Skip malformed records

    # Adjust fields to match header length
    expected_fields = len(headers["B"])
    if len(fields) < expected_fields:
        fields += [""] * (expected_fields - len(fields))
    elif len(fields) > expected_fields:
        fields = fields[:expected_fields]

    recipient_name = fields[5].lower() if len(fields) > 5 else ""
    purpose = fields[16].lower() if len(fields) > 16 else ""
    amount_str = fields[13] if len(fields) > 13 else ""

    try:
        amount = float(amount_str)
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

            if match:
                # Update histogram
                with histogram_lock:
                    bin_key = (score // 10 * 10)
                    histogram[bin_key] += 1
                fields[-1] = str(score)  # Add score to fields
                if score >= 90 and any(keyword in purpose for keyword in transfer_keywords):
                    stats["total_pac_to_pac"] += amount
                    stats["pac_to_pac_count"] += 1
            else:
                fields[-1] = "0"
        else:
            fields[-1] = "0"

    except (ValueError, TypeError):
        stats["exceptions"]["B"] += 1
        exception_log.write(f"Record B Exception (Amount: {amount_str}): {line}\n")
        fields[-1] = "0"

    # Write to 'B' output file with lock
    with b_write_lock:
        output_files["B"].write("|".join(fields) + "\n")

# Second Pass: Process all records with multithreading for 'B' records and progress bar
with ThreadPoolExecutor(max_workers=8) as executor:
    futures = []
    with open(input_file, "r") as infile:
        for line in tqdm(infile, total=total_lines, desc="Second Pass: Processing Records"):
            fields = line.strip().split("|")
            if not fields or not fields[0]:
                continue
            record_type = fields[0]
            if record_type == "B":
                # Submit 'B' record processing to thread pool
                future = executor.submit(process_b_record, line)
                futures.append(future)
            else:
                # Write non-'B' records immediately
                if record_type in output_files:
                    output_files[record_type].write(line)

    # Wait for all 'B' record tasks to complete
    for future in as_completed(futures):
        future.result()  # Ensure all tasks are done

# Close all output files and exception log
for file in output_files.values():
    file.close()
exception_log.close()

# Compute top-5 and bottom-5 purposes by total expenditure
sorted_purposes = sorted(stats["expenditure_by_purpose"].items(), key=lambda x: x[1], reverse=True)
top_5 = sorted_purposes[:5]
bottom_5 = sorted_purposes[-5:] if len(sorted_purposes) >= 5 else sorted_purposes[::-1]

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
print(f"- **Total PAC-to-PAC Transfers**: ${stats['total_pac_to_pac']:,.2f} (based on fuzzy matching with score >= 90 and purpose keywords)")
print(f"- **Number of PAC-to-PAC Transfers**: {stats['pac_to_pac_count']:,}")

print("\n## Top-5 Purposes by Total Expenditure\n")
print("| Purpose | Total Expenditure | Count | Average Expenditure |")
print("|---------|-------------------|-------|--------------------|")
for purpose, total in top_5:
    count = stats["expenditure_count_by_purpose"][purpose]
    avg = total / count if count > 0 else 0
    print(f"| {purpose} | ${total:,.2f} | {count:,} | ${avg:,.2f} |")

print("\n## Bottom-5 Purposes by Total Expenditure\n")
print("| Purpose | Total Expenditure | Count | Average Expenditure |")
print("|---------|-------------------|-------|--------------------|")
for purpose, total in bottom_5:
    count = stats["expenditure_count_by_purpose"][purpose]
    avg = total / count if count > 0 else 0
    print(f"| {purpose} | ${total:,.2f} | {count:,} | ${avg:,.2f} |")

print("\n## Fuzzy Match Score Histogram\n")
print("| Score Range | Count |")
print("|-------------|-------|")
for bin_key in range(0, 101, 10):
    count = histogram[bin_key]
    range_str = f"{bin_key}-{min(bin_key + 9, 100)}" if bin_key < 100 else "100"
    print(f"| {range_str} | {count} |")

print("\nProcessing complete. Output files created for each record type.")
print("Exception log created: exception_log.txt")