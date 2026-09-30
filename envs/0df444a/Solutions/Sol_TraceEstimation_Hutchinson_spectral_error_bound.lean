-- Prove2me | solution 1 for TraceEstimation.Hutchinson.spectral_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:08:02.667685+00:00
-- url     : https://prove2.me/submissions/57e93892-ae0f-4a88-97fc-1eec313a6b52

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Definitions.Def_TraceEstimation_Hutchinson_hutchinsonEstimator
open Matrix TraceEstimation.Hutchinson
open scoped BigOperators
noncomputable section

theorem _root_.solution {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ) (lam : Fin n → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hA : A = U * diagonal lam * Uᵀ) (M : ℕ) (hM : 0 < M) (ε : ℝ) (hε : 0 < ε)
    (ω : Fin M → Fin n → ℝ)
    (hω : ∀ j, lam j ≠ 0 → |(M : ℝ)⁻¹ * ∑ i : Fin M, (Uᵀ *ᵥ ω i) j ^ 2 - 1| ≤ ε) :
    |hutchinsonEstimator A M ω - A.trace| ≤ ε * A.trace := by
  classical
  have hUU : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hU
  have htr : A.trace = ∑ j, lam j := by
    rw [hA, Matrix.trace_mul_cycle, hUU, Matrix.one_mul, Matrix.trace_diagonal]
  have hquad (z : Fin n → ℝ) : z ⬝ᵥ (A *ᵥ z) = ∑ j, lam j * (Uᵀ *ᵥ z) j ^ 2 := by
    rw [hA, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    rw [← Matrix.mulVec_transpose]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hest : hutchinsonEstimator A M ω - A.trace =
      ∑ j, lam j * ((M : ℝ)⁻¹ * ∑ i : Fin M, (Uᵀ *ᵥ ω i) j ^ 2 - 1) := by
    unfold hutchinsonEstimator
    simp_rw [hquad]
    rw [Finset.sum_comm, Finset.mul_sum, htr, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum]
    ring
  rw [hest, htr, Finset.mul_sum]
  calc
    _ ≤ ∑ j, |lam j * ((M : ℝ)⁻¹ * ∑ i : Fin M, (Uᵀ *ᵥ ω i) j ^ 2 - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ε * lam j := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : lam j = 0
      · simp [hj]
      · rw [abs_mul, abs_of_nonneg (hlam j), mul_comm ε]
        exact mul_le_mul_of_nonneg_left (hω j hj) (hlam j)
