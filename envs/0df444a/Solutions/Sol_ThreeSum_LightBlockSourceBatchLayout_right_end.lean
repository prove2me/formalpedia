-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.right_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:50:01.289976+00:00
-- url     : https://prove2.me/submissions/adb491af-9bff-4584-8c1d-aceb54766c41

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution (base count W cut i : ℕ) :
    rightBase base count W cut i+family W cut = slot base count W cut (i+1) := by
  unfold rightBase leftBase flags rawRight rawLeft coeff1 coeff0 slot stride
  ring
end ThreeSum.LightBlockSourceBatchLayout
