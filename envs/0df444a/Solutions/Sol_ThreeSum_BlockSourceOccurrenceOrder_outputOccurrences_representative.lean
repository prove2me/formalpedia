-- Prove2me | solution 1 for ThreeSum.BlockSourceOccurrenceOrder.outputOccurrences_representative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:20.400329+00:00
-- url     : https://prove2.me/submissions/25c0c211-df7d-4a43-a3e0-3f861620ab2b

import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_BlockSourceOccurrenceOrder

set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceOccurrenceOrder
open GlobalEncoding BlockEncoding BlockCoefficientRows OutputDecodeOrder
open OutputDecodeRecords OutputDecodeOccurrenceCode GlobalKeyEnumeration
namespace ThreeSum.BlockSourceOccurrenceOrder
theorem _root_.solution (h J k : ℕ) :
    outputOccurrences (representative h J k) = occurrences h J k := rfl
end ThreeSum.BlockSourceOccurrenceOrder
