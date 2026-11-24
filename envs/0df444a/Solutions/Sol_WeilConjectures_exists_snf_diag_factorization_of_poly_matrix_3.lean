-- Prove2me | solution 3 for WeilConjectures.exists_snf_diag_factorization_of_poly_matrix
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T05:16:17.877739+00:00
-- url     : https://prove2.me/submissions/ea664cbb-cedf-4209-aa64-3cb2ea5ceb67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_exists_normalized_snf_toMatrix_diag_transpose_invariant
import Theorems.Thm_WeilConjectures_exists_unit_cob_of_toMatrix_diagonal

/-!
A63/A64 repair: normalized transpose-invariant toMatrix-diag child;
unit COB via Proved exists_unit_cob_of_toMatrix_diagonal (503effa6).
Avoids Disproved snf_diag_eq_transpose_of_unit_equiv (2c951425).
-/

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      (∀ M i, d M i = d M.transpose i) ∧
      (∀ M, ∃ (P Q : Matrix ι ι (Polynomial K)),
        IsUnit P.det ∧ IsUnit Q.det ∧
          P * M * Q = Matrix.diagonal (d M)) := by
  obtain ⟨d, htr, hdiag⟩ :=
    WeilConjectures.exists_normalized_snf_toMatrix_diag_transpose_invariant
      (K := K) (ι := ι)
  exact ⟨d, htr, WeilConjectures.exists_unit_cob_of_toMatrix_diagonal d hdiag⟩
