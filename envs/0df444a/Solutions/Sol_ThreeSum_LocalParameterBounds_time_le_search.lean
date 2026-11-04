-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.time_le_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:01.320821+00:00
-- url     : https://prove2.me/submissions/5bb17a56-a598-479e-99ca-d2c6028ff64b

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_WeightedCache3SUM_Alias_e3ac3137889c3add
import Theorems.Thm_ThreeSum_LocalParameterBounds_envelope_le_search
import Theorems.Thm_ThreeSum_LightLocalCounts_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_ea9db4f154655ba6
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000
namespace ThreeSum.LocalParameterBounds
theorem _root_.solution {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalParameters.time (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 2000 n :=
  (time_bound _).trans (envelope_le_search hh)
end ThreeSum.LocalParameterBounds
