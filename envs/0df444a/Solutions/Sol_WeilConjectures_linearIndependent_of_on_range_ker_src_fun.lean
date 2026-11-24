-- Prove2me | solution 1 for WeilConjectures.linearIndependent_of_on_range_ker_src_fun
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T05:09:46.12582+00:00
-- url     : https://prove2.me/submissions/4941168f-c228-48f1-a955-1bb2ebf82b52
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_exists_bKer_indexing_of_off_range_src_fun
import Theorems.Thm_WeilConjectures_linearIndependent_of_bKer_indexed_src_fun

/-!
A62/A60a': bKer-indexing child + LI-under-indexing child.
-/

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial K))
    (d : ι → Polynomial K)
    {n : ℕ} (e : Fin n ↪ ι)
    (bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K))
    (v : Fin n → (ι → Polynomial K))
    {m : ℕ}
    (bKer : Module.Basis (Fin m) (Polynomial K)
      (LinearMap.ker (Matrix.toLin' M)))
    (f : ι → (ι → Polynomial K))
    (hmap : ∀ i, Matrix.toLin' M (f i) = d i • bTgt i)
    (hon : ∀ j, f (e j) = v j)
    (hker : ∀ i, (∀ j : Fin n, e j ≠ i) →
      f i ∈ LinearMap.ker (Matrix.toLin' M)) :
    LinearIndependent (Polynomial K) f := by
  obtain ⟨σ, hσ⟩ :=
    WeilConjectures.exists_bKer_indexing_of_off_range_src_fun M e bKer f hker
  exact WeilConjectures.linearIndependent_of_bKer_indexed_src_fun
    M d e bTgt v bKer f hmap hon σ hσ
