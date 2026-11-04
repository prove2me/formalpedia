-- Prove2me | solution 1 for ThreeSum.ThreeSumParameterResources.depth_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:16:13.936672+00:00
-- url     : https://prove2.me/submissions/d92eee0c-aea0-423e-88d5-0be46bcbedad

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
import Theorems.Thm_ThreeSum_EncodedColorResources_local_bounds
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds


set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumParameterResources
open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
set_option maxHeartbeats 2200000
set_option maxRecDepth 14000
namespace ThreeSum.ThreeSumParameterResources
theorem _root_.solution (n : ℕ) : depth n ≤ envelope n := by
  have hh := (local_bounds n).width
  change 512*LightParameterInit.half n+1 ≤ scale n at hh
  have hs := (scale_bounds n).1
  unfold depth envelope
  omega
end ThreeSum.ThreeSumParameterResources
