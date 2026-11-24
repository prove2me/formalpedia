-- Prove2me | solution 1 for WeilConjectures.exists_common_snf_toMatrix_diag_of_transpose
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T22:32:02.219925+00:00
-- url     : https://prove2.me/submissions/e68e7e2f-9060-4f89-b914-4981934b3e7a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_exists_unit_cob_of_toMatrix_diagonal
import Theorems.Thm_WeilConjectures_exists_toMatrix_diag_of_unit_fac

/-!
A64b COMMON-DIAG: `M` and `Mᵀ` share a `toMatrix`-diagonal.

From `hd0` get bases for `M` with diag `d₀ M`. Convert to unit COB via Proved
`exists_unit_cob_of_toMatrix_diagonal` (503effa6). Transpose:
`Qᵀ Mᵀ Pᵀ = diag(d₀ M)`. Recover bases for `Mᵀ` via reverse-COB child (A64c).
-/

open Matrix

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d0 : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hd0 : ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal (d0 M)) :
    ∀ M : Matrix ι ι (Polynomial K),
      ∃ (a : ι → Polynomial K),
        (∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
          LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal a) ∧
        (∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
          LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M.transpose) =
            Matrix.diagonal a) := by
  intro M
  obtain ⟨bSrc, bTgt, hM⟩ := hd0 M
  refine ⟨d0 M, ⟨bSrc, bTgt, hM⟩, ?_⟩
  obtain ⟨P, Q, hP, hQ, hPQ⟩ :=
    WeilConjectures.exists_unit_cob_of_toMatrix_diagonal d0 hd0 M
  have hT : Qᵀ * Mᵀ * Pᵀ = diagonal (d0 M) := by
    calc Qᵀ * Mᵀ * Pᵀ
        = (P * M * Q)ᵀ := by simp [transpose_mul, mul_assoc]
      _ = (diagonal (d0 M))ᵀ := by rw [hPQ]
      _ = diagonal (d0 M) := by simp [diagonal_transpose]
  have hQT : IsUnit Qᵀ.det := by rw [det_transpose]; exact hQ
  have hPT : IsUnit Pᵀ.det := by rw [det_transpose]; exact hP
  exact WeilConjectures.exists_toMatrix_diag_of_unit_fac hQT hPT hT
