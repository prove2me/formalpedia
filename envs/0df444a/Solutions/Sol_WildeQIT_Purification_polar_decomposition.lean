-- Prove2me | solution 1 for WildeQIT.Purification.polar_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T19:28:20.884521+00:00
-- url     : https://prove2.me/submissions/24567f3b-e83a-46ce-94dd-0cf9ff787468

import Mathlib
import Theorems.Thm_WildeQIT_Purification_exists_unitary_eq_mul_of_mul_conjTranspose_eq

open scoped Matrix MatrixOrder
open WildeQIT.Purification

/-- For a positive semidefinite `M`, the square root `S = √M` satisfies `S Sᴴ = M`. -/
theorem pd_sqrt_mul_conjTranspose {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : 0 ≤ M) :
    CFC.sqrt M * (CFC.sqrt M)ᴴ = M := by
  have hsa : (CFC.sqrt M)ᴴ = CFC.sqrt M :=
    (CFC.sqrt_nonneg M).isSelfAdjoint
  rw [hsa, CFC.sqrt_mul_sqrt_self M hM]

theorem solution {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    (∃ U ∈ Matrix.unitaryGroup n ℂ, A = U * CFC.sqrt (Aᴴ * A)) ∧
      (∃ V ∈ Matrix.unitaryGroup n ℂ, A = CFC.sqrt (A * Aᴴ) * V) := by
  constructor
  · -- left polar decomposition: apply unitary freedom to `Aᴴ` and `√(Aᴴ A)`
    have hnn : (0 : Matrix n n ℂ) ≤ Aᴴ * A := by
      simpa [Matrix.star_eq_conjTranspose] using star_mul_self_nonneg A
    have h : Aᴴ * Aᴴᴴ = CFC.sqrt (Aᴴ * A) * (CFC.sqrt (Aᴴ * A))ᴴ := by
      rw [pd_sqrt_mul_conjTranspose _ hnn, Matrix.conjTranspose_conjTranspose]
    obtain ⟨W, hW, hAW⟩ := exists_unitary_eq_mul_of_mul_conjTranspose_eq Aᴴ _ h
    refine ⟨star W, Unitary.star_mem hW, ?_⟩
    have hsa : (CFC.sqrt (Aᴴ * A))ᴴ = CFC.sqrt (Aᴴ * A) :=
      (CFC.sqrt_nonneg (Aᴴ * A)).isSelfAdjoint
    have := congrArg Matrix.conjTranspose hAW
    rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul, hsa] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  · -- right polar decomposition: apply unitary freedom to `A` and `√(A Aᴴ)`
    have hnn : (0 : Matrix n n ℂ) ≤ A * Aᴴ := by
      simpa [Matrix.star_eq_conjTranspose] using mul_star_self_nonneg A
    obtain ⟨V, hV, hAV⟩ := exists_unitary_eq_mul_of_mul_conjTranspose_eq A _
      (pd_sqrt_mul_conjTranspose _ hnn).symm
    exact ⟨V, hV, hAV⟩
