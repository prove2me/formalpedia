-- Prove2me | solution 1 for WeightedCacheParameters.log_pi2_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:01:09.357216+00:00
-- url     : https://prove2.me/submissions/0a7144d7-59ba-4937-a633-da68c03a70fb

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters
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
private theorem log_pi2_raw :
    (313924959372392663 / 500000000000000000 : ℝ) ≤ Real.log (292746547 / 156250000 : ℝ) ∧ Real.log (292746547 / 156250000 : ℝ) ≤ (627849918744785327 / 1000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |(136496547 / 448996547 : ℝ)| < 1) 20
  have heq : (1 + (136496547 / 448996547 : ℝ)) / (1 - (136496547 / 448996547 : ℝ)) = (292746547 / 156250000 : ℝ) := by norm_num
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
theorem _root_.solution :
    (-1765516582307443267 / 500000000000000000 : ℝ) ≤ Real.log (pi2) ∧ Real.log (pi2) ≤ (-1765516582307443263 / 500000000000000000 : ℝ) := by
  have h := log_pi2_raw
  have ht := log_two_raw
  have heq : (pi2) = (292746547 / 156250000 : ℝ) / (2 : ℝ) ^ 6 := by norm_num [pi2]
  rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num
  constructor <;> linarith [h.1, h.2, ht.1, ht.2]
end WeightedCacheParameters
