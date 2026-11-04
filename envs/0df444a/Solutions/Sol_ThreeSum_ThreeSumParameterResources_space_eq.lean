-- Prove2me | solution 1 for ThreeSum.ThreeSumParameterResources.space_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:59:41.607757+00:00
-- url     : https://prove2.me/submissions/dcc203a6-e4f7-4935-9270-dfcda766ef13

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumParameterResources
open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
set_option maxHeartbeats 2200000
set_option maxRecDepth 14000
namespace ThreeSum.ThreeSumParameterResources
theorem _root_.solution (dst n : ℕ) : LightParameterInit.space (work dst) n = dst + cells n :=
  by
  unfold work cells LightParameterInit.space LightLocalParameters.space LightLocalCounts.space LightSelectedPrime.space
    LightPrimePool.space
  omega
end ThreeSum.ThreeSumParameterResources
