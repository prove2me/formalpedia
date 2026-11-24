-- Prove2me | solution 1 for WeilConjectures.exists_dualEquiv_of_conj_eq_smul_symm
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T00:29:43.566859+00:00
-- url     : https://prove2.me/submissions/f2c303c1-2aee-4c4b-83a1-2a0d437bfc43
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_exists_linearEquiv_conj_eq_dualTranspose

/-- From a `V`-conjugation `g.conj F = q • F⁻¹`, rebuild a dual-Frobenius equivalence by
composing `g` with a dual-transpose conjugator for `B := q • F⁻¹`. -/
theorem solution
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (F : V ≃ₗ[K] V) (q : K) (g : V ≃ₗ[K] V)
    (hg : g.conj (F : V →ₗ[K] V) = (q • (F.symm : V →ₗ[K] V))) :
    ∃ (eMid : V ≃ₗ[K] Module.Dual K V),
      eMid.conj (F : V →ₗ[K] V) = (q • (F.symm : V →ₗ[K] V)).dualMap := by
  set B : V →ₗ[K] V := q • (F.symm : V →ₗ[K] V)
  obtain ⟨d, hd⟩ := WeilConjectures.exists_linearEquiv_conj_eq_dualTranspose B
  refine ⟨g.trans d, ?_⟩
  have hconj : (g.trans d).conj (F : V →ₗ[K] V) = d.conj (g.conj (F : V →ₗ[K] V)) := by
    ext x
    simp [LinearEquiv.conj_apply, LinearEquiv.trans_apply]
  calc (g.trans d).conj (F : V →ₗ[K] V)
      = d.conj (g.conj (F : V →ₗ[K] V)) := hconj
    _ = d.conj B := by rw [hg]
    _ = B.dualMap := hd
