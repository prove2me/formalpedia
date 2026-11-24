-- Prove2me | solution 1 for WeilConjectures.exists_mapped_bases_of_on_range_src_and_ker_basis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T04:04:51.415794+00:00
-- url     : https://prove2.me/submissions/0b326c04-7b7a-4dad-9dbd-2fa99b8743d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_exists_li_mapped_src_fun_of_on_range_and_ker_basis

/-!
A57: local Basis.mk from LI+span mapped family; family construction deferred.
-/

open Module

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
    ∃ (bSrc : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      ∀ i, Matrix.toLin' M (bSrc i) = d i • bTgt i := by
  obtain ⟨f, hmap, hli, hsp⟩ :=
    WeilConjectures.exists_li_mapped_src_fun_of_on_range_and_ker_basis
      M d e bTgt v hv hoff bKer
  refine ⟨Basis.mk hli hsp, ?_⟩
  intro i
  simpa [Basis.mk_apply] using hmap i
