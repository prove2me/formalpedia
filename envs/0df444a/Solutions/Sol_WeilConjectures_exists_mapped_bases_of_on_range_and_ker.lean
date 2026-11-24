-- Prove2me | solution 1 for WeilConjectures.exists_mapped_bases_of_on_range_and_ker
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T03:57:43.561974+00:00
-- url     : https://prove2.me/submissions/3f622cef-9f48-4c98-bd82-926357f64412
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_exists_mapped_bases_of_on_range_src_and_ker_basis

/-!
A57/A58: local Free.chooseBasis + reindex Fin; Basis.mk assemble deferred.
-/

open Classical Module

private noncomputable def kerBasisFin
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial K)) :
    Module.Basis (Fin (Fintype.card (Free.ChooseBasisIndex
      (Polynomial K) (LinearMap.ker (Matrix.toLin' M)))))
      (Polynomial K) (LinearMap.ker (Matrix.toLin' M)) :=
  (Free.chooseBasis (Polynomial K) (LinearMap.ker (Matrix.toLin' M))).reindex
    (Fintype.equivFin _)

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hon : ∀ (M : Matrix ι ι (Polynomial K)), ∃ (n : ℕ) (e : Fin n ↪ ι)
      (bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K))
      (v : Fin n → (ι → Polynomial K)),
      (∀ j, Matrix.toLin' M (v j) = d M (e j) • bTgt (e j)) ∧
        (∀ i, (∀ j : Fin n, e j ≠ i) → d M i = 0))
    (_hker : ∀ (M : Matrix ι ι (Polynomial K)),
      Module.Free (Polynomial K) (LinearMap.ker (Matrix.toLin' M)) ∧
        Module.Finite (Polynomial K) (LinearMap.ker (Matrix.toLin' M))) :
    ∀ (M : Matrix ι ι (Polynomial K)),
      ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
        ∀ i, Matrix.toLin' M (bSrc i) = d M i • bTgt i := by
  intro M
  obtain ⟨n, e, bTgt, v, hv, hoff⟩ := hon M
  obtain ⟨bSrc, hb⟩ :=
    WeilConjectures.exists_mapped_bases_of_on_range_src_and_ker_basis
      M (d M) e bTgt v hv hoff (kerBasisFin M)
  exact ⟨bSrc, bTgt, hb⟩
