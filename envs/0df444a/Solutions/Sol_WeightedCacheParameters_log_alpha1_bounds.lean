-- Prove2me | solution 1 for WeightedCacheParameters.log_alpha1_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:01:12.135735+00:00
-- url     : https://prove2.me/submissions/dac43403-7785-48a0-baa5-42964ec8fe16

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
private theorem log_alpha1_raw :
    (354499496541353533 / 1000000000000000000 : ℝ) ≤ Real.log (2672750671 / 1875000000 : ℝ) ∧ Real.log (2672750671 / 1875000000 : ℝ) ≤ (177249748270676767 / 500000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |(797750671 / 4547750671 : ℝ)| < 1) 20
  have heq : (1 + (797750671 / 4547750671 : ℝ)) / (1 - (797750671 / 4547750671 : ℝ)) = (2672750671 / 1875000000 : ℝ) := by norm_num
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
    (-2418089225698427707 / 1000000000000000000 : ℝ) ≤ Real.log (alpha1) ∧ Real.log (alpha1) ≤ (-2418089225698427701 / 1000000000000000000 : ℝ) := by
  have h := log_alpha1_raw
  have ht := log_two_raw
  have heq : (alpha1) = (2672750671 / 1875000000 : ℝ) / (2 : ℝ) ^ 4 := by norm_num [alpha1]
  rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num
  constructor <;> linarith [h.1, h.2, ht.1, ht.2]
end WeightedCacheParameters
