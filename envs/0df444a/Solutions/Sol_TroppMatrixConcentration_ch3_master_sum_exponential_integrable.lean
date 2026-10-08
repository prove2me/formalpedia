-- Prove2me | solution 1 for TroppMatrixConcentration.ch3_master_sum_exponential_integrable
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:10:48.54446+00:00
-- url     : https://prove2.me/submissions/8dafb23b-3729-42a5-8eb1-3b357ca67c29

import Definitions.Def_TroppMatrixConcentration_probability
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder
open TroppMatrixConcentration
set_option autoImplicit false

private lemma matrix_exp_sum_norm_bound {d N : ℕ}
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ k, (A k).IsHermitian) :
    ‖matrixExp (∑ k, A k)‖ ≤ ∏ k, (1 + ‖matrixExp (A k)‖) := by
  let b : Fin N → ℝ := fun k => Real.log (1 + ‖matrixExp (A k)‖)
  have hb (k : Fin N) : A k ≤ algebraMap ℝ _ (b k) := by
    apply le_algebraMap_of_spectrum_le _ (hA k)
    intro x hx
    apply Real.le_log_iff_exp_le (by positivity) |>.2
    have hx' := norm_apply_le_norm_cfc Real.exp (A k) hx Real.continuous_exp.continuousOn (hA k)
    rw [CFC.real_exp_eq_normedSpace_exp (hA k)] at hx'
    have hx'' : Real.exp x ≤ ‖matrixExp (A k)‖ := by
      simpa [matrixExp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)] using hx'
    exact hx''.trans (le_add_of_nonneg_left zero_le_one)
  have hsum : (∑ k, A k).IsHermitian := isSelfAdjoint_sum _ (fun k _ => hA k)
  have hsumle : (∑ k, A k) ≤ algebraMap ℝ _ (∑ k, b k) := by
    simpa only [map_sum] using Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hb k)
  calc
    ‖matrixExp (∑ k, A k)‖ = ‖cfc Real.exp (∑ k, A k)‖ := by
      rw [CFC.real_exp_eq_normedSpace_exp hsum, matrixExp]
    _ ≤ Real.exp (∑ k, b k) := by
      apply norm_cfc_le (Real.exp_pos _).le
      intro x hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
      exact Real.exp_le_exp.mpr ((le_algebraMap_iff_spectrum_le hsum).1 hsumle x hx)
    _ = ∏ k, (1 + ‖matrixExp (A k)‖) := by
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro k hk
      exact Real.exp_log (by positivity)

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    (hMeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hIndep : iIndepFun X μ)
    (hExp : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ) :
    Integrable (fun ω => matrixExp (θ • ∑ k, X k ω)) μ := by
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let f : Matrix (Fin d) (Fin d) ℂ → ℝ := fun A => 1 + ‖matrixExp (θ • A)‖
  have hfcont : Continuous f := by
    dsimp [f, matrixExp]
    fun_prop
  have hfmap (k : Fin N) : Integrable f (μ.map (X k)) := by
    apply (integrable_map_measure hfcont.aestronglyMeasurable (hMeas k).aemeasurable).2
    exact (integrable_const 1).add (hExp k).norm
  have hprod : Integrable (fun ω => ∏ k, f (X k ω)) μ := by
    have hpi := Integrable.fintype_prod hfmap
    rw [← hIndep.map_fun_eq_pi_map (fun k => (hMeas k).aemeasurable)] at hpi
    have hpc : Continuous (fun x : Fin N → Matrix (Fin d) (Fin d) ℂ => ∏ i, f (x i)) :=
      continuous_finsetProd _ (fun i _ => hfcont.comp (continuous_apply i))
    exact (integrable_map_measure hpc.aestronglyMeasurable
      (measurable_pi_lambda _ hMeas).aemeasurable).1 hpi
  apply hprod.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
      (f := fun A : Matrix (Fin d) (Fin d) ℂ => matrixExp (θ • A))
      (by dsimp [matrixExp]; fun_prop) |>.comp_measurable
    exact Finset.measurable_sum _ (fun k _ => hMeas k)
  · filter_upwards [ae_all_iff.2 hHerm] with ω hω
    simpa only [Finset.smul_sum] using
      matrix_exp_sum_norm_bound (fun k => θ • X k ω) (fun k => (hω k).smul (isSelfAdjoint_iff.mpr rfl))
