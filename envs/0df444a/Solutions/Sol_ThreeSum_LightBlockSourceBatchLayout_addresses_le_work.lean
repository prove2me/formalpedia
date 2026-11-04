-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.addresses_le_work
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:57:03.668247+00:00
-- url     : https://prove2.me/submissions/69e1258a-a0d3-4908-9414-79199f84495b

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_right_end_le_masks
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_masks_le_work

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution {base count W cut i : ℕ} (hi : i < count) :
    coeff0 base count W cut i ≤ work base count W cut ∧
    coeff1 base count W cut i ≤ work base count W cut ∧
    rawLeft base count W cut i ≤ work base count W cut ∧
    rawRight base count W cut i ≤ work base count W cut ∧
    flags base count W cut i ≤ work base count W cut ∧
    leftBase base count W cut i ≤ work base count W cut ∧
    rightBase base count W cut i ≤ work base count W cut := by
  have he := (right_end_le_masks hi).trans (masks_le_work base count W cut)
  unfold rightBase leftBase flags rawRight rawLeft coeff1 coeff0 at he ⊢
  omega
end ThreeSum.LightBlockSourceBatchLayout
