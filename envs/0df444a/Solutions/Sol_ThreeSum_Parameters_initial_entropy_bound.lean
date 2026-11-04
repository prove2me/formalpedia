-- Prove2me | solution 1 for ThreeSum.Parameters.initial_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:06:39.109124+00:00
-- url     : https://prove2.me/submissions/d951c150-24c5-476c-9c21-224a63ef719e

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
import Theorems.Thm_ThreeSum_Parameters_power_initial_entropy

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution : entropy initialTheta < (1 / 4 : ℝ) := by
  have hp : (25 : ℝ) ^ 100 < 2 ^ 25 * 24 ^ 96 := by
    exact_mod_cast power_initial_entropy
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 25 ^ 100) hp
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 25 ≠ 0)
    (by positivity : (24 : ℝ) ^ 96 ≠ 0)] at h
  simp only [Real.log_pow] at h
  norm_num at h
  norm_num [initialTheta, entropy, Real.binEntropy]
  rw [Real.log_div (by norm_num : (25 : ℝ) ≠ 0) (by norm_num : (24 : ℝ) ≠ 0),
    div_lt_iff₀ log_two_pos]
  linarith
end ThreeSum.Parameters
