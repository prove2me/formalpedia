-- Prove2me | solution 1 for WeilConjectures.exists_li_mapped_src_fun_of_on_range_and_ker_basis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T04:12:10.385257+00:00
-- url     : https://prove2.me/submissions/7306f0d4-6653-40dd-8c58-0e4aeb4bdd0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_exists_on_range_bSrc_assign
import Theorems.Thm_WeilConjectures_ker_off_range_li_span

/-!
A59/A60 dual: on-range assign child + ker off-range LI/span child.
-/

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial K))
    (d : ι → Polynomial K)
    {n : ℕ} (e : Fin n ↪ ι)
    (bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K))
    (v : Fin n → (ι → Polynomial K))
    (hv : ∀ j, Matrix.toLin' M (v j) = d (e j) • bTgt (e j))
    (hoff : ∀ i, (∀ j : Fin n, e j ≠ i) → d i = 0)
    {m : ℕ}
    (bKer : Module.Basis (Fin m) (Polynomial K)
      (LinearMap.ker (Matrix.toLin' M))) :
    ∃ (f : ι → (ι → Polynomial K)),
      (∀ i, Matrix.toLin' M (f i) = d i • bTgt i) ∧
        LinearIndependent (Polynomial K) f ∧
          ⊤ ≤ Submodule.span (Polynomial K) (Set.range f) := by
  obtain ⟨f, hmap, hon, hker⟩ :=
    WeilConjectures.exists_on_range_bSrc_assign M d e bTgt v hv hoff bKer
  obtain ⟨hli, hsp⟩ :=
    WeilConjectures.ker_off_range_li_span M d e bTgt v bKer f hmap hon hker
  exact ⟨f, hmap, hli, hsp⟩
