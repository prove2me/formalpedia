-- Prove2me | solution 1 for Wigner.wigner_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:48:54.143833+00:00
-- url     : https://prove2.me/submissions/ac022518-667b-4df0-b3cc-2aadfa6999ed

import Mathlib
import Definitions.Def_wigner

open MeasureTheory
open Wigner

theorem solution {ψ : ℝ → ℂ} {ℏ x p : ℝ} (hℏ : 0 < ℏ)
    (hnorm : ∫ y, ‖ψ y‖ ^ 2 = 1) :
    |wigner ψ ℏ x p| ≤ 1 / (Real.pi * ℏ) := by
  have hint : Integrable (fun y => ‖ψ y‖ ^ 2) volume := by
    by_contra h
    rw [integral_undef h] at hnorm
    norm_num at hnorm
  have h1 : Integrable (fun y => ‖ψ (x + y)‖ ^ 2) volume := by
    have := hint.comp_add_left x
    simpa using this
  have h2 : Integrable (fun y => ‖ψ (x - y)‖ ^ 2) volume := by
    have := hint.comp_sub_left x
    simpa using this
  have e1 : ∫ y, ‖ψ (x + y)‖ ^ 2 = 1 := by
    rw [← hnorm]; exact integral_add_left_eq_self (fun y => ‖ψ y‖ ^ 2) x
  have e2 : ∫ y, ‖ψ (x - y)‖ ^ 2 = 1 := by
    rw [← hnorm]; exact integral_sub_left_eq_self (fun y => ‖ψ y‖ ^ 2) volume x
  have hI : ‖wignerIntegral ψ ℏ x p‖ ≤ 1 := by
    unfold wignerIntegral
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpt : ∀ y, ‖wignerIntegrand ψ ℏ x p y‖ ≤ (‖ψ (x + y)‖ ^ 2 + ‖ψ (x - y)‖ ^ 2) / 2 := by
      intro y
      have hexp : ‖Complex.exp (Complex.ofReal (2 * p * y / ℏ) * Complex.I)‖ = 1 := by
        rw [Complex.norm_exp_ofReal_mul_I]
      simp only [wignerIntegrand, norm_mul, Complex.norm_conj, hexp, mul_one]
      nlinarith [sq_nonneg (‖ψ (x + y)‖ - ‖ψ (x - y)‖)]
    calc ∫ y, ‖wignerIntegrand ψ ℏ x p y‖
        ≤ ∫ y, (‖ψ (x + y)‖ ^ 2 + ‖ψ (x - y)‖ ^ 2) / 2 :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
            ((h1.add h2).div_const 2) (Filter.Eventually.of_forall hpt)
      _ = 1 := by
          rw [integral_div, integral_add h1 h2, e1, e2]; norm_num
  have hpos : 0 < Real.pi * ℏ := mul_pos Real.pi_pos hℏ
  unfold wigner
  rw [abs_div, abs_of_pos hpos]
  apply div_le_div_of_nonneg_right _ hpos.le
  exact (Complex.abs_re_le_norm _).trans hI
