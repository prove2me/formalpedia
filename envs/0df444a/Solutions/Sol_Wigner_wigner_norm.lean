-- Prove2me | solution 1 for Wigner.wigner_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:54:22.256188+00:00
-- url     : https://prove2.me/submissions/7a3388bf-2fe0-40dc-b574-65b1af9caf2a

import Mathlib
import Definitions.Def_wigner

open MeasureTheory
open Wigner

open ComplexConjugate FourierTransform

theorem wig_marginal (ψ : SchwartzMap ℝ ℂ) {ℏ x : ℝ} (hℏ : 0 < ℏ) :
    ∫ p, wigner (⇑ψ) ℏ x p = ‖⇑ψ x‖ ^ 2 := by
  have hπℏ : 0 < Real.pi * ℏ := mul_pos Real.pi_pos hℏ
  -- the Schwartz function y ↦ conj ψ(x+y) * ψ(x-y)
  let Bm : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.mul ℝ ℂ).comp Complex.conjCLE.toContinuousLinearMap
  let A : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfAntilipschitz ℝ (g := fun y : ℝ => x + y) (K := 1)
    (by fun_prop) (fun _ _ => by simp [edist_dist, dist_eq_norm]) ψ
  let B : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfAntilipschitz ℝ (g := fun y : ℝ => x - y) (K := 1)
    (by fun_prop) (fun a b => by simp [edist_dist, dist_eq_norm, abs_sub_comm]) ψ
  let G : SchwartzMap ℝ ℂ := SchwartzMap.pairing Bm A B
  have hG : ∀ y, G y = conj (ψ (x + y)) * ψ (x - y) := fun y => rfl
  have hGint : MeasureTheory.Integrable (⇑G) := G.integrable
  have hFint : MeasureTheory.Integrable (𝓕 (⇑G)) := by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 G).integrable
  have hW : ∀ p, wigner (⇑ψ) ℏ x p = (fun w => (𝓕 (⇑G) w).re / (Real.pi * ℏ)) (p / (-(Real.pi * ℏ))) := by
    intro p
    simp only [wigner, wignerIntegral, Real.fourier_real_eq_integral_exp_smul]
    congr 2
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only [wignerIntegrand, hG, smul_eq_mul]
    rw [mul_comm]
    congr 3
    field_simp
  simp_rw [hW]
  rw [MeasureTheory.Measure.integral_comp_div (fun w => (𝓕 (⇑G) w).re / (Real.pi * ℏ)), abs_neg, abs_of_pos hπℏ,
    integral_div, smul_eq_mul, mul_div_cancel₀ _ hπℏ.ne']
  rw [show (∫ a, (𝓕 (⇑G) a).re) = (∫ a, 𝓕 (⇑G) a).re from integral_re hFint]
  have hinv : (∫ w, 𝓕 (⇑G) w) = G 0 := by
    have h := congrFun (Continuous.fourierInv_fourier_eq G.continuous hGint hFint) 0
    rw [Real.fourierInv_eq] at h
    simpa using h
  rw [hinv, hG, add_zero, sub_zero, Complex.conj_mul']
  norm_cast

theorem solution (ψ : SchwartzMap ℝ ℂ) {ℏ : ℝ} (hℏ : 0 < ℏ) :
    ∫ x, ∫ p, wigner (⇑ψ) ℏ x p = ∫ x, ‖⇑ψ x‖ ^ 2 := by
  congr 1
  funext x
  exact wig_marginal ψ hℏ
