-- Prove2me | solution 1 for WeilConjectures.exists_similar_to_companion
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:26:01.919819+00:00
-- url     : https://prove2.me/submissions/6646c83b-f1c2-46e7-8ac0-53d9e00b4927

import Mathlib
import Theorems.Thm_WeilConjectures_exists_invariant_factors_of_matrix

/-!
Instantiate the SNF/RCF package at `A` and `Aᵀ`: both are similar to the same
companion-block matrix `C A = C Aᵀ`.
-/

open Matrix

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) :
    ∃ (C : Matrix ι ι K) (P Q : (ι → K) ≃ₗ[K] (ι → K)),
      P.conj (Matrix.toLin' A) = Matrix.toLin' C ∧
      Q.conj (Matrix.toLin' A.transpose) = Matrix.toLin' C := by
  obtain ⟨C, P, hP, htr⟩ :=
    WeilConjectures.exists_invariant_factors_of_matrix (K := K) (ι := ι)
  refine ⟨C A, P A, P A.transpose, hP A, ?_⟩
  -- `P(Aᵀ).conj Aᵀ = C(Aᵀ) = C(A)`
  calc (P A.transpose).conj (Matrix.toLin' A.transpose)
      = Matrix.toLin' (C A.transpose) := hP A.transpose
    _ = Matrix.toLin' (C A) := by rw [← htr A]
