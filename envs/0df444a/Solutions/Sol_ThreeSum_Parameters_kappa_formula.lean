-- Prove2me | solution 1 for ThreeSum.Parameters.kappa_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:41.27158+00:00
-- url     : https://prove2.me/submissions/4afa1aba-dfed-4dd1-acd0-a96bc7a3803e

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
noncomputable section
namespace ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
private theorem log_256 : Real.log 256 = 8 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 8
  norm_num at h
  exact h
private theorem log_512 : Real.log 512 = 9 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 9
  norm_num at h
  exact h
end ThreeSum.Parameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution :
    kappa * Real.log 2 =
      256 * Real.log (512 / 511) + 255 * Real.log (510 / 511) := by
  have h510 : Real.log (510 : ℝ) = Real.log 2 + Real.log 255 := by
    rw [show (510 : ℝ) = 2 * 255 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num [kappa, entropy, Real.binEntropy]
  rw [Real.log_div (by norm_num : (512 : ℝ) ≠ 0) (by norm_num : (511 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (256 : ℝ) ≠ 0) (by norm_num : (255 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (510 : ℝ) ≠ 0) (by norm_num : (511 : ℝ) ≠ 0),
    log_256, log_512, h510]
  field_simp
  ring
end ThreeSum.Parameters
