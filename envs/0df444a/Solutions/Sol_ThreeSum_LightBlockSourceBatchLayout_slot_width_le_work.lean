-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.slot_width_le_work
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:57:02.472206+00:00
-- url     : https://prove2.me/submissions/521f7915-0b7b-463e-b092-e129fc599578

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_right_end_le_masks

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution {base count W cut i : ℕ} (hi : i < count) :
    slot base count W cut i+W ≤ work base count W cut := by
  have hr := right_end_le_masks (base := base) (W := W) (cut := cut) hi
  unfold rightBase leftBase flags rawRight rawLeft coeff1 coeff0 family at hr
  unfold work rowOut bitBase
  omega
end ThreeSum.LightBlockSourceBatchLayout
