-- Prove2me | solution 1 for WeilConjectures.exists_mapped_bases_of_zero_pad_snf_diag
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T03:31:57.397453+00:00
-- url     : https://prove2.me/submissions/f5082793-b01e-4ebe-8608-afb3f990df8a

import Mathlib
import Theorems.Thm_WeilConjectures_exists_mapped_bases_of_snf_preimage_family

/-!
A54: local Classical preimage family from SNF+pad (short);
assembly of full mapped bases deferred to child.
-/

open Classical

private theorem exists_snf_preimage_family_of_zero_pad_snf_diag
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hpad : ∀ M, ∃ (n : ℕ)
        (snf : Module.Basis.SmithNormalForm
          (LinearMap.range (Matrix.toLin' M)) ι n),
        (∀ j, d M (snf.f j) = snf.a j) ∧
          (∀ i, (∀ j : Fin n, snf.f j ≠ i) → d M i = 0)) :
    ∀ M, ∃ (n : ℕ)
      (snf : Module.Basis.SmithNormalForm
        (LinearMap.range (Matrix.toLin' M)) ι n)
      (v : Fin n → (ι → Polynomial K)),
      (∀ j, d M (snf.f j) = snf.a j) ∧
      (∀ i, (∀ j : Fin n, snf.f j ≠ i) → d M i = 0) ∧
      (∀ j, Matrix.toLin' M (v j) = d M (snf.f j) • snf.bM (snf.f j)) := by
  intro M
  obtain ⟨n, snf, hon, hoff⟩ := hpad M
  have hmem (j : Fin n) :
      (snf.bN j : ι → Polynomial K) ∈ LinearMap.range (Matrix.toLin' M) :=
    (snf.bN j).property
  let v : Fin n → (ι → Polynomial K) := fun j => Classical.choose (hmem j)
  have hv (j : Fin n) :
      Matrix.toLin' M (v j) = (snf.bN j : ι → Polynomial K) :=
    Classical.choose_spec (hmem j)
  refine ⟨n, snf, v, hon, hoff, ?_⟩
  intro j
  rw [hv, snf.snf, hon]

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hpad : ∀ M, ∃ (n : ℕ)
        (snf : Module.Basis.SmithNormalForm
          (LinearMap.range (Matrix.toLin' M)) ι n),
        (∀ j, d M (snf.f j) = snf.a j) ∧
          (∀ i, (∀ j : Fin n, snf.f j ≠ i) → d M i = 0)) :
    ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      ∀ i, Matrix.toLin' M (bSrc i) = d M i • bTgt i := by
  exact WeilConjectures.exists_mapped_bases_of_snf_preimage_family d
    (exists_snf_preimage_family_of_zero_pad_snf_diag d hpad)
