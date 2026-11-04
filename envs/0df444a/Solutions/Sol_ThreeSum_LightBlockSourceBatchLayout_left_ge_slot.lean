-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.left_ge_slot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:10.058853+00:00
-- url     : https://prove2.me/submissions/054e36ca-1c70-42c6-b1ef-32a41fe63cc6

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution (base count W cut i : ℕ) :
    slot base count W cut i ≤ leftBase base count W cut i := by
  unfold leftBase flags rawRight rawLeft coeff1 coeff0
  omega
end ThreeSum.LightBlockSourceBatchLayout
