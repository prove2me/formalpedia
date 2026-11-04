-- Prove2me | solution 1 for ThreeSum.Parameters.tangentAB_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:14.766975+00:00
-- url     : https://prove2.me/submissions/7e36da5f-52c3-4d15-879f-1f74923bfcb3

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_Parameters_power_tangent_right

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution : tangentA + tangentB / 2 < (1413 / 1000 : ℝ) := by
  have hp : (10000 : ℝ) ^ 500 < 2 ^ 1413 * 1411 ^ 500 := by
    exact_mod_cast power_tangent_right
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 10000 ^ 500) hp
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 1413 ≠ 0)
    (by positivity : (1411 : ℝ) ^ 500 ≠ 0)] at h
  simp only [Real.log_pow] at h
  have h10000 : Real.log (10000 : ℝ) = 2 * Real.log 100 := by
    rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h1411 : Real.log (1411 : ℝ) = Real.log 83 + Real.log 17 := by
    rw [show (1411 : ℝ) = 83 * 17 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  rw [h10000, h1411] at h
  norm_num at h
  have heq : tangentA + tangentB / 2 =
      (Real.log 100 - Real.log 83 / 2 - Real.log 17 / 2) / Real.log 2 := by
    unfold tangentA tangentB
    ring
  rw [heq, div_lt_iff₀ log_two_pos]
  linarith
end ThreeSum.Parameters
