-- Prove2me | solution 1 for PI.SSE.norm_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:35.272647+00:00
-- url     : https://prove2.me/submissions/cbe39813-6db4-460b-92c6-297b1f7935da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaNz
import Theorems.Thm_PI_SSE_norm_qe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution (τ : ℂ) (hy : 0 < τ.im) (n : ℕ) :
    ‖(2 * ((n + 1 : ℕ) : ℂ) + 1) * ((-1) ^ (n + 1) * qe τ (n + 1))‖
      ≤ (3 * Real.exp (-(2 * Real.pi * τ.im))) ^ (n + 1) := by
  have hc : ‖(2 * ((n + 1 : ℕ) : ℂ) + 1)‖ = ((2 * (n + 1) + 1 : ℕ) : ℝ) := by
    rw [show (2 * ((n + 1 : ℕ) : ℂ) + 1) = ((2 * (n + 1) + 1 : ℕ) : ℂ) by push_cast; ring]
    exact Complex.norm_natCast _
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_qe, hc]
  have hA : ((2 * (n + 1) + 1 : ℕ) : ℝ) ≤ 3 ^ (n + 1) := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 2 by norm_num) (n + 1)
    push_cast at h ⊢
    norm_num at h
    linarith
  have hB : Real.exp (-(Real.pi * τ.im * (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)))) ≤
      Real.exp (-(2 * Real.pi * τ.im)) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hy.le)
      (mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1))]
  calc ((2 * (n + 1) + 1 : ℕ) : ℝ) * Real.exp (-(Real.pi * τ.im * (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))))
      ≤ 3 ^ (n + 1) * Real.exp (-(2 * Real.pi * τ.im)) ^ (n + 1) :=
        mul_le_mul hA hB (Real.exp_pos _).le (by positivity)
    _ = (3 * Real.exp (-(2 * Real.pi * τ.im))) ^ (n + 1) := (mul_pow _ _ _).symm
end PI.SSE
