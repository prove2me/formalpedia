-- Prove2me | solution 1 for SpectralSharpness.NormalWindow.theorem_9_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:31:29.1402+00:00
-- url     : https://prove2.me/submissions/45b3e5c9-b862-42d9-bf5c-c4920926cf51

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_BandLimited
import Definitions.Def_SpectralSharpness_NormalWindow_ExponentialType
import Theorems.Thm_SpectralSharpness_NormalWindow_lemma_9_1

section
set_option autoImplicit false

namespace SpectralSharpness.Dev.LineExt
open SpectralSharpness.NormalWindow

lemma differentiable_of_spectrum {n : ℕ} (S : Set (Fin n → ℤ)) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : HasSpectrumIn S f) : Differentiable ℝ f := by
  obtain ⟨F, c, -, hF⟩ := hf
  have h1 : Differentiable ℝ (fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ k ∈ F, c k * Complex.exp (Complex.I * (freqDot k x : ℂ))) := by
    unfold freqDot
    fun_prop
  have h2 : f = fun x => (∑ k ∈ F, c k * Complex.exp (Complex.I * (freqDot k x : ℂ))).re := by
    funext x
    rw [← hF x]; simp
  rw [h2]
  exact Complex.reCLM.differentiable.comp h1

end SpectralSharpness.Dev.LineExt
end

section
set_option autoImplicit false

open MeasureTheory

namespace SpectralSharpness.Dev.T93
open SpectralSharpness.NormalWindow SpectralSharpness.Dev.LineExt

lemma window_aux (φ : ℝ → ℝ) (L : ℝ) (hL : 0 < L) (hφ : Differentiable ℝ φ)
    (hb : ∀ t, |deriv φ t| ≤ L) (γ : ℝ) (hγ : 0 < γ) (tm tp : ℝ) (htm : tm < 0) (htp : 0 < tp)
    (hfm : φ tm ≤ -γ) (hfp : γ ≤ φ tp) :
    ENNReal.ofReal (2 * γ / L) ≤ volume {t : ℝ | t ∈ Set.Icc tm tp ∧ |φ t| < γ} := by
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc tm tp ∧ |φ t| < γ} with hS
  have hlip : LipschitzWith (Real.toNNReal L) φ := by
    refine lipschitzWith_of_nnnorm_deriv_le hφ fun x => ?_
    have := hb x
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hL.le]
    simpa using this
  have hsub : Set.Ioo (-γ) γ ⊆ φ '' S := by
    intro y hy
    have hc : ContinuousOn φ (Set.Icc tm tp) := hφ.continuous.continuousOn
    have := intermediate_value_Icc (by linarith : tm ≤ tp) hc
    obtain ⟨t, ht, hty⟩ := this (show y ∈ Set.Icc (φ tm) (φ tp) from
      ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    exact ⟨t, ⟨ht, by rw [hty]; exact abs_lt.mpr hy⟩, hty⟩
  have h1 : volume (φ '' S) ≤ (Real.toNNReal L : ENNReal) * volume S := by
    have := hlip.hausdorffMeasure_image_le (d := 1) zero_le_one S
    simpa [hausdorffMeasure_real] using this
  have h2 : ENNReal.ofReal (2 * γ) ≤ ENNReal.ofReal L * volume S := by
    calc ENNReal.ofReal (2 * γ) = volume (Set.Ioo (-γ) γ) := by
          rw [Real.volume_Ioo]; congr 1; ring
      _ ≤ volume (φ '' S) := measure_mono hsub
      _ ≤ _ := h1
  rw [ENNReal.ofReal_div_of_pos hL]
  exact ENNReal.div_le_of_le_mul' h2

end SpectralSharpness.Dev.T93

namespace SpectralSharpness.NormalWindow
open SpectralSharpness.Dev.T93 SpectralSharpness.Dev.LineExt in
theorem chk_theorem_9_3 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (d A γ : ℝ) (hd : 0 ≤ d)
    (hf : IsBandLimitedBall d f) (hA : ∀ x, |f x| ≤ A) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (p v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) (tm tp : ℝ) (htm : tm < 0) (htp : 0 < tp)
    (hfm : f (p + tm • v) ≤ -γ) (hfp : γ ≤ f (p + tp • v)) :
    ENNReal.ofReal (2 * γ / (d * A)) ≤
      volume {t : ℝ | t ∈ Set.Icc tm tp ∧ |f (p + t • v)| < γ} := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  by_cases hL : d * A = 0
  · rw [hL, div_zero]; simp
  have hL' : 0 < d * A := lt_of_le_of_ne (mul_nonneg hd hA0) (Ne.symm hL)
  have hdf := differentiable_of_spectrum _ f hf
  have hlem := ((lemma_9_1 d A hd).1 f hf hA).1 v hv
  have hder : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (p + s • v)) (fderiv ℝ f (p + t • v) v) t := by
    intro t
    have h := (hdf (p + t • v)).hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => p + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add p
    exact h.comp_hasDerivAt t h2
  exact window_aux (fun s : ℝ => f (p + s • v)) (d * A) hL'
    (fun t => (hder t).differentiableAt) (fun t => by rw [(hder t).deriv]; exact hlem _) γ hγ0 tm tp
    htm htp hfm hfp

end SpectralSharpness.NormalWindow
end

theorem solution : type_of% @SpectralSharpness.NormalWindow.chk_theorem_9_3 := @SpectralSharpness.NormalWindow.chk_theorem_9_3
