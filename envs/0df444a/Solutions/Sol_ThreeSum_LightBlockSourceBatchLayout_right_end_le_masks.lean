-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.right_end_le_masks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:53:57.606888+00:00
-- url     : https://prove2.me/submissions/eaa87d08-e176-454d-aafd-56e5dc2efd76

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_slot_mono
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_right_end

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution {base count W cut i : ℕ} (hi : i < count) :
    rightBase base count W cut i+family W cut ≤ maskBase base count W cut := by
  rw [right_end]
  exact slot_mono base count W cut (by omega)
end ThreeSum.LightBlockSourceBatchLayout
