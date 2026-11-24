-- Prove2me | solution 1 for WeilConjectures.exists_mapped_bases_of_snf_preimage_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T03:43:13.464162+00:00
-- url     : https://prove2.me/submissions/1c37526b-593c-4d8a-b7aa-f4956182bb21
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_exists_mapped_bases_of_on_range_and_ker

/-!
A56: local unpack of on-range assign + local Free/Finite of ker;
glue deferred to child.
-/

open Classical Module

private theorem exists_on_range_src_assign
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hpre : ∀ M, ∃ (n : ℕ)
      (snf : Basis.SmithNormalForm
        (LinearMap.range (Matrix.toLin' M)) ι n)
      (v : Fin n → (ι → Polynomial K)),
      (∀ j, d M (snf.f j) = snf.a j) ∧
      (∀ i, (∀ j : Fin n, snf.f j ≠ i) → d M i = 0) ∧
      (∀ j, Matrix.toLin' M (v j) = d M (snf.f j) • snf.bM (snf.f j))) :
    ∀ M, ∃ (n : ℕ) (e : Fin n ↪ ι)
      (bTgt : Basis ι (Polynomial K) (ι → Polynomial K))
      (v : Fin n → (ι → Polynomial K)),
      (∀ j, Matrix.toLin' M (v j) = d M (e j) • bTgt (e j)) ∧
        (∀ i, (∀ j : Fin n, e j ≠ i) → d M i = 0) := by
  intro M
  obtain ⟨n, snf, v, _hon, hoff, hv⟩ := hpre M
  exact ⟨n, snf.f, snf.bM, v, hv, hoff⟩

private theorem ker_free_finite_of_toLin
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial K)) :
    Module.Free (Polynomial K) (LinearMap.ker (Matrix.toLin' M)) ∧
      Module.Finite (Polynomial K) (LinearMap.ker (Matrix.toLin' M)) :=
  ⟨inferInstance, inferInstance⟩

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hpre : ∀ M, ∃ (n : ℕ)
      (snf : Module.Basis.SmithNormalForm
        (LinearMap.range (Matrix.toLin' M)) ι n)
      (v : Fin n → (ι → Polynomial K)),
      (∀ j, d M (snf.f j) = snf.a j) ∧
      (∀ i, (∀ j : Fin n, snf.f j ≠ i) → d M i = 0) ∧
      (∀ j, Matrix.toLin' M (v j) = d M (snf.f j) • snf.bM (snf.f j))) :
    ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      ∀ i, Matrix.toLin' M (bSrc i) = d M i • bTgt i := by
  exact WeilConjectures.exists_mapped_bases_of_on_range_and_ker d
    (exists_on_range_src_assign d hpre)
    (fun M => ker_free_finite_of_toLin M)
