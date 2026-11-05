-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.log_bankArg_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:11.090346+00:00
-- url     : https://prove2.me/submissions/ba9e4ddb-0a1d-4b10-984f-6a46c76d586b

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_bankArg_lower_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_bankArg_upper_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace WeightedCacheParameters_e1ae71d
theorem _root_.solution :
    (194416086704412431 / 1000000000000000000 : ℝ) ≤ Real.log bankArg ∧ Real.log bankArg ≤ (194416086704412433 / 1000000000000000000 : ℝ) := by
  have hp : (242920311477828953 / 200000000000000000 : ℝ) ≤ bankArg ∧ bankArg ≤ (607300778694572383 / 500000000000000000 : ℝ) := by
    constructor <;> norm_num [bankArg, yRoot]
  have hl := Real.log_le_log (by norm_num : 0 < (242920311477828953 / 200000000000000000 : ℝ)) hp.1
  have hu := Real.log_le_log (lt_of_lt_of_le (by norm_num : 0 < (242920311477828953 / 200000000000000000 : ℝ)) hp.1) hp.2
  exact ⟨(log_bankArg_lower_bounds).1.trans hl, hu.trans (log_bankArg_upper_bounds).2⟩
end WeightedCacheParameters_e1ae71d
