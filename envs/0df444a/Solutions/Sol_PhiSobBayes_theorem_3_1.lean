-- Prove2me | solution 1 for PhiSobBayes.theorem_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:10:16.340393+00:00
-- url     : https://prove2.me/submissions/73a8ecfb-dfac-4915-8a30-8b58cbfa16f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhiSobBayes_eq_49
import Theorems.Thm_PhiSobBayes_theorem_3_1_forward
import Definitions.Def_PhiSobBayes_IsLogConcave

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

open PhiSobBayes in
/-- the integral `∫ Φ''(f) ‖∇f‖²` is nonnegative for `J`-valued `f`. -/
theorem PhiSobBayes_aux_nonneg {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (J : Set ℝ)
    (Φ : ℝ → ℝ) (hΦ : AdmissiblePhi J Φ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ testClass n J) :
    0 ≤ ∫ x, deriv (deriv Φ) (f x) * ‖gradient f x‖ ^ 2 ∂μ :=
  integral_nonneg fun x => mul_nonneg (hΦ.2.1 _ (hf.2 x)).le (sq_nonneg _)

open PhiSobBayes in
theorem PhiSobBayes_one_snr {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : IsLogConcave μ)
    (J : Set ℝ) (hJ : IsOpenInterval J) (Φ : ℝ → ℝ) (hΦ : AdmissiblePhi J Φ) (b T : ℝ)
    (hb : 0 < b) (hT : 0 < T)
    (H : ∀ f ∈ testClass n J, ENNReal.ofReal (b * phiEnt μ Φ f) ≤ bayesRisk μ J Φ T f) :
    PhiSobolev μ J Φ (1 / (b * T)) := by
  intro f hf
  have h1 := (H f hf).trans (eq_49 μ hμ J hJ Φ hΦ f hf T hT)
  have hE := PhiSobBayes_aux_nonneg μ J Φ hΦ f hf
  set E := ∫ x, deriv (deriv Φ) (f x) * ‖gradient f x‖ ^ 2 ∂μ
  have h2 : b * phiEnt μ Φ f ≤ 1 / (2 * T) * E :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have : phiEnt μ Φ f ≤ (1 / (2 * T) * E) / b := by
    rw [le_div_iff₀ hb]; linarith
  calc phiEnt μ Φ f ≤ (1 / (2 * T) * E) / b := this
    _ = 1 / (b * T) / 2 * E := by field_simp

theorem solution {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : PhiSobBayes.IsLogConcave μ)
    (C : ℝ) (hC : 0 < C)
    (J : Set ℝ) (hJ : PhiSobBayes.IsOpenInterval J) (Φ : ℝ → ℝ) (hΦ : PhiSobBayes.AdmissiblePhi J Φ) :
    (PhiSobBayes.PhiSobolev μ J Φ C ↔
      ∀ f ∈ PhiSobBayes.testClass n J, ∀ t : ℝ, 0 < t →
        ENNReal.ofReal (PhiSobBayes.phiEnt μ Φ f / (1 + C * t)) ≤ PhiSobBayes.bayesRisk μ J Φ t f) ∧
    (∀ b T : ℝ, 0 < b → 0 < T →
      (∀ f ∈ PhiSobBayes.testClass n J,
        ENNReal.ofReal (b * PhiSobBayes.phiEnt μ Φ f) ≤ PhiSobBayes.bayesRisk μ J Φ T f) →
      PhiSobBayes.PhiSobolev μ J Φ (1 / (b * T))) := by
  have := hμ.1
  refine ⟨⟨fun hS f hf t ht => PhiSobBayes.theorem_3_1_forward μ C hC J hJ Φ hΦ hS f hf t ht,
    fun H => ?_⟩, fun b T hb hT H => PhiSobBayes_one_snr μ hμ J hJ Φ hΦ b T hb hT H⟩
  intro f hf
  have hE := PhiSobBayes_aux_nonneg μ J Φ hΦ f hf
  set E := ∫ x, deriv (deriv Φ) (f x) * ‖gradient f x‖ ^ 2 ∂μ with hEdef
  have key : ∀ t : ℝ, 0 < t → PhiSobBayes.phiEnt μ Φ f ≤ (C + 1 / t) / 2 * E := by
    intro t ht
    have hb : 0 < 1 / (1 + C * t) := by positivity
    have := PhiSobBayes_one_snr μ hμ J hJ Φ hΦ (1 / (1 + C * t)) t hb ht (by
      intro g hg
      have := H g hg t ht
      convert this using 2
      field_simp) f hf
    convert this using 2
    field_simp
    ring
  by_contra hlt
  push Not at hlt
  set δ := PhiSobBayes.phiEnt μ Φ f - C / 2 * E
  have hδ : 0 < δ := by simp only [δ]; linarith
  have := key ((E + 1) / δ) (by positivity)
  have h3 : 1 / ((E + 1) / δ) / 2 * E < δ := by
    rw [one_div_div]
    rw [div_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have : (C + 1 / ((E + 1) / δ)) / 2 * E = C / 2 * E + 1 / ((E + 1) / δ) / 2 * E := by ring
  simp only [δ] at *
  linarith
