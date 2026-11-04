-- Prove2me | solution 1 for WeightedCacheParameters.log_bankArg_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:06:59.545211+00:00
-- url     : https://prove2.me/submissions/722a98a3-4d1f-4cb7-99b5-8445afa0a790

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters
import Theorems.Thm_WeightedCacheParameters_log_bankArg_lower_bounds
import Theorems.Thm_WeightedCacheParameters_log_bankArg_upper_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace WeightedCacheParameters
theorem _root_.solution :
    (194413244396031453 / 1000000000000000000 : ℝ) ≤ Real.log bankArg ∧ Real.log bankArg ≤ (6075413887375983 / 31250000000000000 : ℝ) := by
  have hp : (151824763140233107 / 125000000000000000 : ℝ) ≤ bankArg ∧ bankArg ≤ (1214598105121864857 / 1000000000000000000 : ℝ) := by
    constructor <;> norm_num [bankArg, yRoot]
  have hl := Real.log_le_log (by norm_num : 0 < (151824763140233107 / 125000000000000000 : ℝ)) hp.1
  have hu := Real.log_le_log (lt_of_lt_of_le (by norm_num : 0 < (151824763140233107 / 125000000000000000 : ℝ)) hp.1) hp.2
  exact ⟨(log_bankArg_lower_bounds).1.trans hl, hu.trans (log_bankArg_upper_bounds).2⟩
end WeightedCacheParameters
