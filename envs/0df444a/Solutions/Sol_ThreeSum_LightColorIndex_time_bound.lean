-- Prove2me | solution 1 for ThreeSum.LightColorIndex.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:36:54.040117+00:00
-- url     : https://prove2.me/submissions/b9b047e6-a1b7-4d24-b831-42235beb5c07

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSum_LightColorIndex

set_option autoImplicit false
open ThreeSum ThreeSum.LightColorIndex
open Light LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightColorIndex
theorem _root_.solution (W : ℕ) : time W ≤ 300*(W+1) := by
  unfold time LightMaskErase.time
  omega
end ThreeSum.LightColorIndex
