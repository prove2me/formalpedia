-- Prove2me | solution 1 for WeightedCacheParameters.Gn_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:05:13.728069+00:00
-- url     : https://prove2.me/submissions/db36debb-5dbb-4d6f-a211-284b8f3faa5e

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters
import Theorems.Thm_WeightedCacheParameters_log_three_bounds
noncomputable section
namespace WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
private theorem log_two_raw :
    (693147180559945309 / 1000000000000000000 : ℝ) ≤ Real.log (2 / 1 : ℝ) ∧ Real.log (2 / 1 : ℝ) ≤ (69314718055994531 / 100000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |(1 / 3 : ℝ)| < 1) 20
  have heq : (1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ)) = (2 / 1 : ℝ) := by norm_num
  rw [heq] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]
end WeightedCacheParameters
set_option autoImplicit false
noncomputable section
open WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace WeightedCacheParameters
theorem _root_.solution : (142141038618045131 / 1000000000000000000 : ℝ) ≤ Gn ∧ Gn ≤ (35535259654511283 / 250000000000000000 : ℝ) := by
  have htwo := log_two_raw
  have hthree := log_three_bounds
  norm_num [Gn, pi0, pi1, pi2, alpha0, alpha1, alpha2, cutSlope, dropSlope] at *
  constructor <;> linarith
end WeightedCacheParameters
