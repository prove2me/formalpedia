-- Prove2me | solution 1 for TroppMatrixConcentration.ch3_lieb_regularity_shift_integrable
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:21:58.567773+00:00
-- url     : https://prove2.me/submissions/c51782be-cf87-420a-b229-39e444bf7edb

import Definitions.Def_TroppMatrixConcentration_probability
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FinCases

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
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (X : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeas : Measurable X) (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hExp : Integrable (fun ω => matrixExp (X ω)) μ) :
    Integrable (fun ω => matrixExp (H + X ω)) μ ∧
      Integrable (fun ω => traceExp (H + X ω)) μ := by
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hInt : Integrable (fun ω => matrixExp (H + X ω)) μ := by
    have hBoundInt : Integrable (fun ω =>
        (1 + ‖matrixExp H‖) * (1 + ‖matrixExp (X ω)‖)) μ :=
      ((integrable_const 1).add hExp.norm).const_mul _
    apply hBoundInt.mono' ?_ ?_
    · have hc : Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => matrixExp (H + A)) := by
        dsimp [matrixExp]
        fun_prop
      exact hc.aestronglyMeasurable.comp_measurable hMeas
    · filter_upwards [hHerm] with ω hω
      have hh : ∀ k : Fin 2, (![H, X ω] k).IsHermitian := by
        intro k
        fin_cases k
        · exact hH
        · exact hω
      simpa [Fin.sum_univ_two, Fin.prod_univ_two] using
        matrix_exp_sum_norm_bound ![H, X ω] hh
  exact ⟨hInt, Complex.reCLM.integrable_comp
    ((Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap.integrable_comp hInt)⟩
