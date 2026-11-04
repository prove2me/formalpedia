-- Prove2me | solution 1 for ThreeSum.ThreeSumParameterResources.local_word_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:27:25.86065+00:00
-- url     : https://prove2.me/submissions/22b3673d-9846-4f81-b253-f677e82ba8b9

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
import Theorems.Thm_ThreeSum_ThreeSumParameterResources_local_envelope_le
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds
import Theorems.Thm_ThreeSum_LightBandRawAResources_word_bound
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_word_bound
import Theorems.Thm_ThreeSum_LightLocalCoverResources_word_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_word_bound


set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumParameterResources
open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
set_option maxHeartbeats 2200000
set_option maxRecDepth 14000
namespace ThreeSum.ThreeSumParameterResources
theorem _root_.solution (n : ℕ) : LightLocalParameters.word (LightParameterInit.half n) ≤ scale n :=
  (LocalParameterBounds.word_bound _).trans ((local_envelope_le n).trans (scale_bounds n).2.2.2.1)
end ThreeSum.ThreeSumParameterResources
