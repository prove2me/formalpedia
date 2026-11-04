-- Prove2me | solution 1 for ThreeSum.LightMaskUnion.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:35:25.366874+00:00
-- url     : https://prove2.me/submissions/4e207240-0fb0-46f1-b751-74a02ac53aff

import Definitions.Def_Submission_ThreeSum_MaskUnion
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightMaskUnion

set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskUnion
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open MaskUnion
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightMaskUnion
theorem _root_.solution (W : ℕ) : time W ≤ 800*(W+1)^2 := by
  unfold time powTableTime LightMaskErase.time
  nlinarith
end ThreeSum.LightMaskUnion
