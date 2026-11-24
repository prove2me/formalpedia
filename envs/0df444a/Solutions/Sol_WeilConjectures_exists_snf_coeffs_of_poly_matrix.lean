-- Prove2me | solution 1 for WeilConjectures.exists_snf_coeffs_of_poly_matrix
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:38:18.432563+00:00
-- url     : https://prove2.me/submissions/32074360-17c6-4fda-a4dd-0f34b82340d5

import Mathlib
import Theorems.Thm_WeilConjectures_exists_snf_of_range_toLin_poly_matrix
import Theorems.Thm_WeilConjectures_exists_diag_bases_of_range_snf

/-!
A46: range-SNF for every `toLin' M`.
A47: reindex/pad to full-ι bases with `toMatrix = diagonal (d M)`.
-/

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
        LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal (d M) := by
  exact WeilConjectures.exists_diag_bases_of_range_snf
    (WeilConjectures.exists_snf_of_range_toLin_poly_matrix (K := K) (ι := ι))
