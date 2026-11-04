-- Prove2me | solution 1 for ThreeSum.OutputDecodeOccurrenceCode.source_code_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:31.156209+00:00
-- url     : https://prove2.me/submissions/5c2b5f34-e8f5-4697-94b4-ef07b60f0e4e

import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
import Theorems.Thm_ThreeSum_OutputDecodeOccurrenceCode_code_indices
import Theorems.Thm_List_getD_map_of_lt
import Theorems.Thm_ThreeSum_OutputDecodeOrder_indices_length


set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeOccurrenceCode
open OutputDecodeOrder OutputDecodeRecords GlobalEncoding
set_option maxHeartbeats 1500000
namespace ThreeSum.OutputDecodeOccurrenceCode
theorem _root_.solution (h J k : ℕ) {j : ℕ} (hj : j < J) :
    (indices (scheduleSize h) J (code (scheduleSize h) (layerCount h) J k)).getD j 0 =
      occurrenceIndex h J k j := by
  rw [code_indices (schedule_pos h) (layerCount_pos h)]
  have hi : j < (indices (scheduleSize h*layerCount h) J k).length := by
    rw [indices_length]
    exact hj
  rw [List.getD_map_of_lt _ hi 0 0]
  rfl
end ThreeSum.OutputDecodeOccurrenceCode
