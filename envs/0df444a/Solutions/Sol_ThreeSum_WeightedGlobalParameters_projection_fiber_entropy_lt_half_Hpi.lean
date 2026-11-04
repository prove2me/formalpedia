-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.projection_fiber_entropy_lt_half_Hpi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:57.836216+00:00
-- url     : https://prove2.me/submissions/ca5c61d5-3dbb-4d14-9fd6-e3a09c518120

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_bounds
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_projection_fiber_entropy_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution :
    Real.binEntropy alpha2 / Real.log 2 < Hpi / 2 := by
  linarith [projection_fiber_entropy_bound, Hpi_bounds.1]
end ThreeSum.WeightedGlobalParameters
