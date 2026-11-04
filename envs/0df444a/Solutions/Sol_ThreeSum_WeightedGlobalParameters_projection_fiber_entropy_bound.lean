-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.projection_fiber_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:56.855566+00:00
-- url     : https://prove2.me/submissions/7bcedb7d-1df4-49f0-bdcb-52bcc7e0792e

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_ThreeSum_Parameters_initial_entropy_bound
import Theorems.Thm_ThreeSum_Parameters_log_two_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution :
    Real.binEntropy alpha2 / Real.log 2 < (1 / 4 : ℝ) := by
  have hm := Real.binEntropy_strictMonoOn
    (by norm_num [alpha2] : alpha2 ∈ Set.Icc (0 : ℝ) 2⁻¹)
    (by norm_num [Parameters.initialTheta] :
      Parameters.initialTheta ∈ Set.Icc (0 : ℝ) 2⁻¹)
    (by norm_num [alpha2, Parameters.initialTheta] :
      alpha2 < Parameters.initialTheta)
  have hd := div_lt_div_of_pos_right hm log_two_pos
  have hb := Parameters.initial_entropy_bound
  unfold Parameters.entropy at hb
  exact hd.trans hb
end ThreeSum.WeightedGlobalParameters
