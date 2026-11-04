-- Prove2me | solution 1 for ThreeSum.BlockSourceOccurrenceOrder.row_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:50.710795+00:00
-- url     : https://prove2.me/submissions/4a94d932-8e33-47b1-a2be-7f7cda473e09

import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_BlockSourceOccurrenceOrder
import Theorems.Thm_ThreeSum_BlockCoefficientRows_occurrenceIndices_fin
attribute [local simp] ThreeSum.BlockCoefficientRows.occurrenceIndices_fin



set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceOccurrenceOrder
open GlobalEncoding BlockEncoding BlockCoefficientRows OutputDecodeOrder
open OutputDecodeRecords OutputDecodeOccurrenceCode GlobalKeyEnumeration
namespace ThreeSum.BlockSourceOccurrenceOrder
theorem _root_.solution {h J k j : ℕ} (hj : j < J) :
    occurrenceIndices (outputOccurrences (representative h J k)) j =
      (indices (scheduleSize h) J k).getD j 0 := by
  rw [occurrenceIndices_fin _ ⟨j,hj⟩]
  rfl
end ThreeSum.BlockSourceOccurrenceOrder
