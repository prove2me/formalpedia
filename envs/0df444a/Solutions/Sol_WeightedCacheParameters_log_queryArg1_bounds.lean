-- Prove2me | solution 1 for WeightedCacheParameters.log_queryArg1_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:07:00.767298+00:00
-- url     : https://prove2.me/submissions/2937e406-35e2-4ced-83c4-dadf707294d4

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters
import Theorems.Thm_WeightedCacheParameters_log_queryArg1_lower_bounds
import Theorems.Thm_WeightedCacheParameters_log_queryArg1_upper_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace WeightedCacheParameters
theorem _root_.solution :
    (36293388703209917 / 500000000000000000 : ℝ) ≤ Real.log queryArg1 ∧ Real.log queryArg1 ≤ (72586777406419837 / 1000000000000000000 : ℝ) := by
  have hp : (107528611258165787 / 100000000000000000 : ℝ) ≤ queryArg1 ∧ queryArg1 ≤ (1075286112581657871 / 1000000000000000000 : ℝ) := by
    constructor <;> norm_num [queryArg1, zRoot]
  have hl := Real.log_le_log (by norm_num : 0 < (107528611258165787 / 100000000000000000 : ℝ)) hp.1
  have hu := Real.log_le_log (lt_of_lt_of_le (by norm_num : 0 < (107528611258165787 / 100000000000000000 : ℝ)) hp.1) hp.2
  exact ⟨(log_queryArg1_lower_bounds).1.trans hl, hu.trans (log_queryArg1_upper_bounds).2⟩
end WeightedCacheParameters
