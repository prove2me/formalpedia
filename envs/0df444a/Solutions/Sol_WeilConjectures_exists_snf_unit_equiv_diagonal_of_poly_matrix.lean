-- Prove2me | solution 1 for WeilConjectures.exists_snf_unit_equiv_diagonal_of_poly_matrix
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:18:56.717793+00:00
-- url     : https://prove2.me/submissions/609faafd-2918-4835-ac98-5830cf3fb023

import Mathlib
import Theorems.Thm_WeilConjectures_exists_snf_coeffs_of_poly_matrix
import Theorems.Thm_WeilConjectures_exists_unit_cob_of_toMatrix_diagonal

/-!
A44: obtain SNF coeffs `d` with bases diagonalizing `toLin' M`.
A45: convert to unit COB matrices `P, Q`.
-/

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      ∀ M, ∃ (P Q : Matrix ι ι (Polynomial K)),
        IsUnit P.det ∧ IsUnit Q.det ∧
          P * M * Q = Matrix.diagonal (d M) := by
  obtain ⟨d, hdiag⟩ :=
    WeilConjectures.exists_snf_coeffs_of_poly_matrix (K := K) (ι := ι)
  exact ⟨d, WeilConjectures.exists_unit_cob_of_toMatrix_diagonal d hdiag⟩
