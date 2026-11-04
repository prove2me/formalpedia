-- Prove2me | solution 1 for ThreeSum.TernaryParameters.log_y_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:51:41.277643+00:00
-- url     : https://prove2.me/submissions/c5935616-4d7e-4377-b478-34813a2ac8bd

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
noncomputable section
namespace ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
private theorem log_two_bounds :
    (13862943611198906187 / 20000000000000000000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (17328679513998632737 / 25000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((1 / 3 : ℝ) : ℝ)| < 1) 20
  have hratio : ((1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ)) : ℝ) = 2 := by
    norm_num []
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]
private theorem log_normalized_y_bounds :
    (37363379875988122211 / 100000000000000000000 : ℝ) ≤ Real.log normalized_y ∧ Real.log normalized_y ≤ (9340844968997030553 / 25000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((566256201 / 3066256201 : ℝ) : ℝ)| < 1) 20
  have hratio : ((1 + (566256201 / 3066256201 : ℝ)) / (1 - (566256201 / 3066256201 : ℝ)) : ℝ) = normalized_y := by
    norm_num [normalized_y]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]
end ThreeSum.TernaryParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.TernaryParameters
theorem _root_.solution :
    (-170580774291995470633 / 100000000000000000000 : ℝ) ≤ Real.log y ∧ Real.log y ≤ (-170580774291995470593 / 100000000000000000000 : ℝ) := by
  have hu := log_normalized_y_bounds
  have htwo := log_two_bounds
  have heq : y = normalized_y / (2 : ℝ) ^ 3 := by norm_num [y, normalized_y]
  rw [heq, Real.log_div (by norm_num [normalized_y]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]
end ThreeSum.TernaryParameters
