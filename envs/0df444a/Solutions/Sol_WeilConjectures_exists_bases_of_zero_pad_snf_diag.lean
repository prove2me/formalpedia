-- Prove2me | solution 1 for WeilConjectures.exists_bases_of_zero_pad_snf_diag
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T03:24:40.477306+00:00
-- url     : https://prove2.me/submissions/72244ad4-5a99-4761-9e6b-a8612fac715c

import Mathlib
import Theorems.Thm_WeilConjectures_exists_mapped_bases_of_zero_pad_snf_diag

/-!
A53: obtain mapped bases from SNF+pad child; convert to `toMatrix = diagonal`
via a local Mathlib-style lemma (A51 probe: short, no placeholders).
-/

open Module

private theorem toMatrix_eq_diagonal_of_mapped_basis
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] [DecidableEq ι]
    (bSrc bTgt : Basis ι R M) (f : M →ₗ[R] M) (d : ι → R)
    (h : ∀ i, f (bSrc i) = d i • bTgt i) :
    LinearMap.toMatrix bSrc bTgt f = Matrix.diagonal d := by
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply, h, map_smul, Basis.repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]
  aesop

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hpad : ∀ M, ∃ (n : ℕ)
        (snf : Module.Basis.SmithNormalForm
          (LinearMap.range (Matrix.toLin' M)) ι n),
        (∀ j, d M (snf.f j) = snf.a j) ∧
          (∀ i, (∀ j : Fin n, snf.f j ≠ i) → d M i = 0)) :
    ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal (d M) := by
  intro M
  obtain ⟨bSrc, bTgt, hmap⟩ :=
    WeilConjectures.exists_mapped_bases_of_zero_pad_snf_diag d hpad M
  exact ⟨bSrc, bTgt, toMatrix_eq_diagonal_of_mapped_basis bSrc bTgt _ (d M) hmap⟩
