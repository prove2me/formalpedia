-- Prove2me | solution 1 for TroppMatrixConcentration.master_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:12:28.826973+00:00
-- url     : https://prove2.me/submissions/0e3219da-c9c9-414e-99c6-803027561f48

import Theorems.Thm_TroppMatrixConcentration_ch3_laplace_tails
import Theorems.Thm_TroppMatrixConcentration_ch3_laplace_expectations
import Theorems.Thm_TroppMatrixConcentration_trace_cgf_subadditivity
import Theorems.Thm_TroppMatrixConcentration_ch3_master_sum_exponential_integrable
import Theorems.Thm_TroppMatrixConcentration_ch3_tail_spectral_comparison
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
open TroppMatrixConcentration
set_option autoImplicit false

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    (hMeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hInt : ∀ k, Integrable (X k) μ) (hIndep : iIndepFun X μ)
    (hExp : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ) :
    (0 < θ →
      (∫ ω, lambdaMax (∑ k, X k ω) ∂μ) ≤
        Real.log (traceExp (cumulantSum μ X θ)) / θ ∧
      ∀ t : ℝ, (μ {ω | t ≤ lambdaMax (∑ k, X k ω)}).toReal ≤
        Real.exp (-θ * t) * traceExp (cumulantSum μ X θ)) ∧
    (θ < 0 →
      Real.log (traceExp (cumulantSum μ X θ)) / θ ≤
        (∫ ω, lambdaMin (∑ k, X k ω) ∂μ) ∧
      ∀ t : ℝ, (μ {ω | lambdaMin (∑ k, X k ω) ≤ t}).toReal ≤
        Real.exp (-θ * t) * traceExp (cumulantSum μ X θ)) := by
  have hYMeas : Measurable (fun ω => ∑ k, X k ω) :=
    Finset.measurable_sum _ (fun k _ => hMeas k)
  have hYHerm : ∀ᵐ ω ∂μ, (∑ k, X k ω).IsHermitian := by
    filter_upwards [ae_all_iff.2 hHerm] with ω hω
    exact isSelfAdjoint_sum _ (fun k _ => hω k)
  have hYInt : Integrable (fun ω => ∑ k, X k ω) μ :=
    integrable_finsetSum _ (fun k _ => hInt k)
  have hYExp := ch3_master_sum_exponential_integrable μ X θ hMeas hHerm hIndep hExp
  have hTrInt : Integrable (fun ω => traceExp (θ • ∑ k, X k ω)) μ := by
    exact Complex.reCLM.integrable_comp
      ((Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap.integrable_comp hYExp)
  have hTrNonneg : ∀ᵐ ω ∂μ, 0 ≤ traceExp (θ • ∑ k, X k ω) := by
    filter_upwards [hYHerm] with ω hω
    exact (ch3_tail_spectral_comparison _ hω θ).1
  have hTrPos (hθ : θ ≠ 0) : 0 < ∫ ω, traceExp (θ • ∑ k, X k ω) ∂μ := by
    have hPos : ∀ᵐ ω ∂μ, 0 < traceExp (θ • ∑ k, X k ω) := by
      filter_upwards [hYHerm] with ω hω
      rcases lt_or_gt_of_ne hθ with hneg | hpos
      · exact (Real.exp_pos _).trans_le
          ((ch3_tail_spectral_comparison _ hω θ).2.2 hneg)
      · exact (Real.exp_pos _).trans_le
          ((ch3_tail_spectral_comparison _ hω θ).2.1 hpos)
    apply (integral_pos_iff_support_of_nonneg_ae hTrNonneg hTrInt).2
    have hFull : Function.support (fun ω => traceExp (θ • ∑ k, X k ω)) =ᵐ[μ]
        (Set.univ : Set Ω) := by
      filter_upwards [hPos] with ω hω
      apply propext
      change (traceExp (θ • ∑ k, X k ω) ≠ 0) ↔ True
      exact iff_true_intro hω.ne'
    rw [measure_congr hFull]
    simp
  have hCGF : (∫ ω, traceExp (θ • ∑ k, X k ω) ∂μ) ≤
      traceExp (cumulantSum μ X θ) := by
    simpa only [Finset.smul_sum] using
      trace_cgf_subadditivity μ X θ hMeas hHerm hIndep hExp
  have hTails := ch3_laplace_tails μ (fun ω => ∑ k, X k ω) θ hYMeas hYHerm hYExp
  have hMeans := ch3_laplace_expectations μ (fun ω => ∑ k, X k ω) θ
    hYMeas hYHerm hYInt hYExp
  constructor
  · intro hθ
    constructor
    · exact (hMeans.1 hθ).trans (div_le_div_of_nonneg_right
        (Real.log_le_log (hTrPos hθ.ne') hCGF) hθ.le)
    · intro t
      exact (hTails.1 hθ t).trans (mul_le_mul_of_nonneg_left hCGF (Real.exp_pos _).le)
  · intro hθ
    constructor
    · exact (div_le_div_of_nonpos_of_le hθ.le
        (Real.log_le_log (hTrPos hθ.ne) hCGF)).trans (hMeans.2 hθ)
    · intro t
      exact (hTails.2 hθ t).trans (mul_le_mul_of_nonneg_left hCGF (Real.exp_pos _).le)
