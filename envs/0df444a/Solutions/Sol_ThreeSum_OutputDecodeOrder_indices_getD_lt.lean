-- Prove2me | solution 1 for ThreeSum.OutputDecodeOrder.indices_getD_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:23:50.899736+00:00
-- url     : https://prove2.me/submissions/54ebc9cd-3e70-4f9d-9947-827d2a07b117

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Theorems.Thm_ThreeSum_OutputDecodeOrder_indices_length
import Theorems.Thm_ThreeSum_OutputDecodeOrder_indices_lt

set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeOrder
open RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000
variable {α β : Type*}
namespace ThreeSum.OutputDecodeOrder
theorem _root_.solution {m J k j : ℕ} (hm : 0 < m) (hj : j < J) :
    (indices m J k).getD j 0 < m := by
  rw [List.getD_eq_getElem _ _ (by rw [indices_length]; exact hj)]
  exact indices_lt hm J k _ (List.getElem_mem _)
end ThreeSum.OutputDecodeOrder
