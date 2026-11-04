-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.Hpi_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:08:44.19702+00:00
-- url     : https://prove2.me/submissions/213e01bb-c8e6-48eb-b64b-317f7a43985a

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_bounds
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_WeightedCacheParameters_Hn_bounds


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : (81443/100000 : ℝ)≤Hpi ∧ Hpi≤(81444/100000 : ℝ) := by
  have hx := WeightedCacheParameters.Hn_bounds
  have hl := log_two_bounds
  constructor
  · apply (le_div_iff₀ log_two_pos).mpr
    linarith [hx.1,hl.2]
  · apply (div_le_iff₀ log_two_pos).mpr
    linarith [hx.2,hl.1]
end ThreeSum.WeightedGlobalParameters
