-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.log_queryArg1_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:33.137824+00:00
-- url     : https://prove2.me/submissions/8a8ffa3c-46de-4197-a38b-27bf387258b3

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_queryArg1_lower_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_queryArg1_upper_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace WeightedCacheParameters_e1ae71d
theorem _root_.solution :
    (14515179898819027 / 200000000000000000 : ℝ) ≤ Real.log queryArg1 ∧ Real.log queryArg1 ≤ (36287949747047569 / 500000000000000000 : ℝ) := by
  have hp : (537637207888609881 / 500000000000000000 : ℝ) ≤ queryArg1 ∧ queryArg1 ≤ (1075274415777219763 / 1000000000000000000 : ℝ) := by
    constructor <;> norm_num [queryArg1, zRoot]
  have hl := Real.log_le_log (by norm_num : 0 < (537637207888609881 / 500000000000000000 : ℝ)) hp.1
  have hu := Real.log_le_log (lt_of_lt_of_le (by norm_num : 0 < (537637207888609881 / 500000000000000000 : ℝ)) hp.1) hp.2
  exact ⟨(log_queryArg1_lower_bounds).1.trans hl, hu.trans (log_queryArg1_upper_bounds).2⟩
end WeightedCacheParameters_e1ae71d
