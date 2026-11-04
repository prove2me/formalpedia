-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.bankEntropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:15:58.006376+00:00
-- url     : https://prove2.me/submissions/63574092-78af-4576-b6c8-e4872b523769

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_bounds
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_WeightedCacheParameters_Bn_bounds


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : (78197/100000 : ℝ)≤bankEntropy ∧ bankEntropy≤(78198/100000 : ℝ) := by
  have hx := WeightedCacheParameters.Bn_bounds
  have hl := log_two_bounds
  constructor
  · apply (le_div_iff₀ log_two_pos).mpr
    linarith [hx.1,hl.2]
  · apply (div_le_iff₀ log_two_pos).mpr
    linarith [hx.2,hl.1]
end ThreeSum.WeightedGlobalParameters
