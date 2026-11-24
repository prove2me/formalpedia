-- Prove2me | solution 1 for WeilConjectures.exists_invariant_factors_of_matrix
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:42:53.271985+00:00
-- url     : https://prove2.me/submissions/574c2fbb-f437-476d-b75c-e78eaf063eec

import Mathlib
import Theorems.Thm_WeilConjectures_exists_snf_of_polynomial_matrix

/-!
From poly-SNF: set `C A := rcf (invFactors (charmatrix A))` and `P A := sim A`.
Transpose invariance of `C` follows from `charmatrix_transpose` +
`invFactors M = invFactors Mᵀ`.
-/

open Matrix Polynomial

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (C : Matrix ι ι K → Matrix ι ι K)
      (P : Matrix ι ι K → ((ι → K) ≃ₗ[K] (ι → K))),
      (∀ A, (P A).conj (Matrix.toLin' A) = Matrix.toLin' (C A)) ∧
      (∀ A, C A = C A.transpose) := by
  obtain ⟨invFactors, rcf, sim, htr, hsim⟩ :=
    WeilConjectures.exists_snf_of_polynomial_matrix (K := K) (ι := ι)
  refine ⟨fun A => rcf (invFactors (charmatrix A)), sim, hsim, ?_⟩
  intro A
  -- `C A = rcf (invFactors charA) = rcf (invFactors charAᵀ) = rcf (invFactors (char A)ᵀ)
  --      = rcf (invFactors char(Aᵀ)) = C Aᵀ`
  calc rcf (invFactors (charmatrix A))
      = rcf (invFactors (charmatrix A).transpose) := by rw [htr]
    _ = rcf (invFactors (charmatrix A.transpose)) := by rw [← charmatrix_transpose]
