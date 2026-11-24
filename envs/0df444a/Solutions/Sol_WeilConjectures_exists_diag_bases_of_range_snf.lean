-- Prove2me | solution 1 for WeilConjectures.exists_diag_bases_of_range_snf
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:51:54.177366+00:00
-- url     : https://prove2.me/submissions/1fe3bf84-2a6a-4b1f-8506-c86882a8ff04

import Mathlib
import Theorems.Thm_WeilConjectures_exists_zero_pad_diag_of_range_snf
import Theorems.Thm_WeilConjectures_exists_bases_of_zero_pad_snf_diag

/-!
A50: zero-pad SNF coeffs to full ι.
A49: reindex bases so toMatrix = diagonal (d M).
-/

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (hSNF : ∀ M : Matrix ι ι (Polynomial K),
      ∃ (n : ℕ),
        Nonempty
          (Module.Basis.SmithNormalForm
            (LinearMap.range (Matrix.toLin' M)) ι n)) :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
        LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal (d M) := by
  obtain ⟨d, hpad⟩ :=
    WeilConjectures.exists_zero_pad_diag_of_range_snf (K := K) (ι := ι) hSNF
  exact ⟨d, WeilConjectures.exists_bases_of_zero_pad_snf_diag d hpad⟩
