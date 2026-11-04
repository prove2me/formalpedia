-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.Halpha_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:09:32.02218+00:00
-- url     : https://prove2.me/submissions/e522d3ad-9e7a-40ae-ab89-cdf459f3a944

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_bounds
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_WeightedCacheParameters_An_bounds


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : (51129/100000 : ℝ)≤Halpha ∧ Halpha≤(51130/100000 : ℝ) := by
  have hx := WeightedCacheParameters.An_bounds
  have hl := log_two_bounds
  constructor
  · apply (le_div_iff₀ log_two_pos).mpr
    linarith [hx.1,hl.2]
  · apply (div_le_iff₀ log_two_pos).mpr
    linarith [hx.2,hl.1]
end ThreeSum.WeightedGlobalParameters
