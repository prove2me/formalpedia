-- Prove2me | solution 1 for TroppMatrixConcentration.ch3_laplace_tails
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:12:26.954142+00:00
-- url     : https://prove2.me/submissions/d557ef57-e016-4d32-9a68-eaaaa6fef6f1

import Definitions.Def_TroppMatrixConcentration_probability
import Theorems.Thm_TroppMatrixConcentration_ch3_tail_spectral_comparison
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Positivity

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false

namespace TroppMatrixConcentration

lemma ch3_tail_trace_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d : ℕ} (Z : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hZ : Integrable Z μ) : Integrable (fun ω => (Matrix.trace (Z ω)).re) μ := by
  exact Complex.reCLM.integrable_comp
    ((Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap.integrable_comp hZ)

lemma ch3_tail_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → ℝ) (s : Set Ω)
    (a : ℝ) (hF : Integrable F μ) (hpos : ∀ᵐ ω ∂μ, 0 ≤ F ω)
    (hs : ∀ᵐ ω ∂μ, ω ∈ s → Real.exp a ≤ F ω) :
    (μ s).toReal ≤ Real.exp (-a) * ∫ ω, F ω ∂μ := by
  have hsub : μ s ≤ μ {ω | Real.exp a ≤ F ω} :=
    measure_mono_ae hs
  have hreal : (μ s).toReal ≤ (μ {ω | Real.exp a ≤ F ω}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) hsub
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hpos hF (Real.exp a)
  have hmul : Real.exp a * (μ s).toReal ≤ ∫ ω, F ω ∂μ :=
    (mul_le_mul_of_nonneg_left hreal (Real.exp_pos a).le).trans hmarkov
  calc
    (μ s).toReal = Real.exp (-a) * (Real.exp a * (μ s).toReal) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hmul (Real.exp_pos _).le

end TroppMatrixConcentration

open TroppMatrixConcentration

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (Y : Ω → Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    (hMeas : Measurable Y) (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hExp : Integrable (fun ω => matrixExp (θ • Y ω)) μ) :
    (0 < θ → ∀ t : ℝ,
      (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤
        Real.exp (-θ * t) * (∫ ω, traceExp (θ • Y ω) ∂μ)) ∧
    (θ < 0 → ∀ t : ℝ,
      (μ {ω | lambdaMin (Y ω) ≤ t}).toReal ≤
        Real.exp (-θ * t) * (∫ ω, traceExp (θ • Y ω) ∂μ)) := by
  have hInt : Integrable (fun ω => traceExp (θ • Y ω)) μ :=
    ch3_tail_trace_integrable μ _ hExp
  have hnonneg : ∀ᵐ ω ∂μ, 0 ≤ traceExp (θ • Y ω) := by
    filter_upwards [hHerm] with ω hω
    exact (ch3_tail_spectral_comparison _ hω θ).1
  constructor
  · intro hθ t
    have h := ch3_tail_event_bound μ (fun ω => traceExp (θ • Y ω))
      {ω | t ≤ lambdaMax (Y ω)} (θ * t) hInt hnonneg ?_
    · simpa only [neg_mul] using h
    · filter_upwards [hHerm] with ω hω
      intro ht
      exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hθ.le)).trans
        ((ch3_tail_spectral_comparison _ hω θ).2.1 hθ)
  · intro hθ t
    have h := ch3_tail_event_bound μ (fun ω => traceExp (θ • Y ω))
      {ω | lambdaMin (Y ω) ≤ t} (θ * t) hInt hnonneg ?_
    · simpa only [neg_mul] using h
    · filter_upwards [hHerm] with ω hω
      intro ht
      exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht hθ.le)).trans
        ((ch3_tail_spectral_comparison _ hω θ).2.2 hθ)
