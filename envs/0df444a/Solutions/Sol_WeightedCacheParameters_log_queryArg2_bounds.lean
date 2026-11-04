-- Prove2me | solution 1 for WeightedCacheParameters.log_queryArg2_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:09:30.479472+00:00
-- url     : https://prove2.me/submissions/96c2336c-bfa0-4930-863f-863e59e32d39

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters
import Theorems.Thm_WeightedCacheParameters_log_queryArg2_lower_bounds
import Theorems.Thm_WeightedCacheParameters_log_queryArg2_upper_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace WeightedCacheParameters
theorem _root_.solution :
    (15493328653985123 / 200000000000000000 : ℝ) ≤ Real.log queryArg2 ∧ Real.log queryArg2 ≤ (38733321634962809 / 500000000000000000 : ℝ) := by
  have hp : (540273094184934183 / 500000000000000000 : ℝ) ≤ queryArg2 ∧ queryArg2 ≤ (1080546188369868367 / 1000000000000000000 : ℝ) := by
    constructor <;> norm_num [queryArg2, zRoot]
  have hl := Real.log_le_log (by norm_num : 0 < (540273094184934183 / 500000000000000000 : ℝ)) hp.1
  have hu := Real.log_le_log (lt_of_lt_of_le (by norm_num : 0 < (540273094184934183 / 500000000000000000 : ℝ)) hp.1) hp.2
  exact ⟨(log_queryArg2_lower_bounds).1.trans hl, hu.trans (log_queryArg2_upper_bounds).2⟩
end WeightedCacheParameters
