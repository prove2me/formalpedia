-- Prove2me | solution 1 for WeightedCacheParameters.Qn_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:13:10.237518+00:00
-- url     : https://prove2.me/submissions/ff2e9526-e8d1-47fc-b9ea-aa07a8e26f37

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters
import Theorems.Thm_WeightedCacheParameters_log_zRoot_bounds
import Theorems.Thm_WeightedCacheParameters_log_queryArg1_bounds
import Theorems.Thm_WeightedCacheParameters_log_queryArg2_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace WeightedCacheParameters
theorem _root_.solution : (48568421114506253 / 1000000000000000000 : ℝ) ≤ Qn ∧ Qn ≤ (48568421114506283 / 1000000000000000000 : ℝ) := by
  have hqueryArg1 := log_queryArg1_bounds
  have hqueryArg2 := log_queryArg2_bounds
  have hzRoot := log_zRoot_bounds
  norm_num [Qn, pi0, pi1, pi2, alpha0, alpha1, alpha2, cutSlope, dropSlope] at *
  constructor <;> linarith
end WeightedCacheParameters
