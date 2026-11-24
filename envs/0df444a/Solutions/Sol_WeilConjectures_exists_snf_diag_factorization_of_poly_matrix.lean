-- Prove2me | solution 1 for WeilConjectures.exists_snf_diag_factorization_of_poly_matrix
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:13:12.287279+00:00
-- url     : https://prove2.me/submissions/d41fdc40-a0e6-4d56-ae7a-8737045e3d14
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_exists_snf_unit_equiv_diagonal_of_poly_matrix
import Theorems.Thm_WeilConjectures_snf_diag_eq_transpose_of_unit_equiv

/-!
A42 dual: obtain Smith unit-equivalence `d`/`hfac`, then transpose via uniqueness.
-/

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      (∀ M i, d M i = d M.transpose i) ∧
      (∀ M, ∃ (P Q : Matrix ι ι (Polynomial K)),
        IsUnit P.det ∧ IsUnit Q.det ∧
          P * M * Q = Matrix.diagonal (d M)) := by
  obtain ⟨d, hfac⟩ :=
    WeilConjectures.exists_snf_unit_equiv_diagonal_of_poly_matrix (K := K) (ι := ι)
  exact ⟨d, WeilConjectures.snf_diag_eq_transpose_of_unit_equiv d hfac, hfac⟩
