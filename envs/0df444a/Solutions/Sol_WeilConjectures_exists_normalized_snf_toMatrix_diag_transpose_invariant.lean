-- Prove2me | solution 1 for WeilConjectures.exists_normalized_snf_toMatrix_diag_transpose_invariant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T14:17:27.888159+00:00
-- url     : https://prove2.me/submissions/2a8beee6-6077-4b53-93b1-2427eff86165
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_exists_snf_coeffs_of_poly_matrix
import Theorems.Thm_WeilConjectures_exists_transpose_invariant_snf_toMatrix_diag_of_coeffs

/-!
A64: normalized transpose-invariant SNF `toMatrix`-diag.
Reuses Proved `exists_snf_coeffs_of_poly_matrix` (7d346459); reduces the
transpose-normalization to a single child (A64a).
-/

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      (∀ M i, d M i = d M.transpose i) ∧
      (∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
        LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) =
          Matrix.diagonal (d M)) := by
  obtain ⟨d0, hd0⟩ :=
    WeilConjectures.exists_snf_coeffs_of_poly_matrix (K := K) (ι := ι)
  exact WeilConjectures.exists_transpose_invariant_snf_toMatrix_diag_of_coeffs d0 hd0
