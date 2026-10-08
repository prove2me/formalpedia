-- Prove2me | solution 1 for TroppMatrixConcentration.ch3_laplace_expectations
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:12:27.788316+00:00
-- url     : https://prove2.me/submissions/8dc8a3b8-f61f-4a1f-9a97-7ae549a159c1

import Definitions.Def_TroppMatrixConcentration_probability
import Theorems.Thm_TroppMatrixConcentration_ch3_expect_extrema_integrable
import Theorems.Thm_TroppMatrixConcentration_ch3_tail_spectral_comparison
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false

namespace TroppMatrixConcentration

/-- Scalar Jensen step for an integrable majorant of an exponential. -/
lemma ch3_expect_log_integral_majorant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ) (θ : ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hbound : ∀ᵐ ω ∂μ, Real.exp (θ * f ω) ≤ g ω) :
    θ * (∫ ω, f ω ∂μ) ≤ Real.log (∫ ω, g ω ∂μ) := by
  have hscaled : Integrable (fun ω => θ * f ω) μ := hf.const_mul θ
  have he : Integrable (fun ω => Real.exp (θ * f ω)) μ :=
    hg.mono' (Real.continuous_exp.comp_aestronglyMeasurable hscaled.aestronglyMeasurable)
      (hbound.mono fun ω hω => by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hω)
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hscaled he
  have hle : Real.exp (θ * (∫ ω, f ω ∂μ)) ≤ ∫ ω, g ω ∂μ := by
    calc
      Real.exp (θ * (∫ ω, f ω ∂μ)) = Real.exp (∫ ω, θ * f ω ∂μ) := by rw [integral_const_mul]
      _ ≤ ∫ ω, Real.exp (θ * f ω) ∂μ := hj
      _ ≤ ∫ ω, g ω ∂μ := integral_mono_ae he hg hbound
  exact (Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hle)).mpr hle

end TroppMatrixConcentration

open TroppMatrixConcentration

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (Y : Ω → Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    (hMeas : Measurable Y) (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hInt : Integrable Y μ)
    (hExp : Integrable (fun ω => matrixExp (θ • Y ω)) μ) :
    (0 < θ → (∫ ω, lambdaMax (Y ω) ∂μ) ≤
      Real.log (∫ ω, traceExp (θ • Y ω) ∂μ) / θ) ∧
    (θ < 0 → Real.log (∫ ω, traceExp (θ • Y ω) ∂μ) / θ ≤
      (∫ ω, lambdaMin (Y ω) ∂μ)) := by
  have ht : Integrable (fun ω => traceExp (θ • Y ω)) μ := by
    exact Complex.reCLM.integrable_comp
      ((Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap.integrable_comp hExp)
  obtain ⟨hmax, hmin⟩ := ch3_expect_extrema_integrable μ Y hMeas hHerm hInt
  constructor
  · intro hθ
    apply (le_div_iff₀ hθ).mpr
    rw [mul_comm]
    apply ch3_expect_log_integral_majorant μ _ _ θ hmax ht
    filter_upwards [hHerm] with ω hω
    exact (ch3_tail_spectral_comparison (Y ω) hω θ).2.1 hθ
  · intro hθ
    apply (div_le_iff_of_neg hθ).mpr
    rw [mul_comm]
    apply ch3_expect_log_integral_majorant μ _ _ θ hmin ht
    filter_upwards [hHerm] with ω hω
    exact (ch3_tail_spectral_comparison (Y ω) hω θ).2.2 hθ
