-- Prove2me | solution 1 for ThreeSum.LightQueryWeights.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:53:06.009727+00:00
-- url     : https://prove2.me/submissions/67b4d42f-9074-41be-8aa2-deef97b8112f

import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightQueryWeights

set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryWeights
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightQueryWeights
theorem _root_.solution (W : ℕ) : time W ≤ 500*(W+1)^2 := by
  unfold time powTableTime LightMaskErase.time
  nlinarith
end ThreeSum.LightQueryWeights
