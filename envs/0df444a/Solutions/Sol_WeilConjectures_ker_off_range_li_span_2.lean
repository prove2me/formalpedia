-- Prove2me | solution 2 for WeilConjectures.ker_off_range_li_span
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T04:57:02.420402+00:00
-- url     : https://prove2.me/submissions/730a523a-86ee-4b4a-9bca-d65bf73cf292
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_linearIndependent_of_on_range_ker_src_fun
import Theorems.Thm_WeilConjectures_span_top_of_on_range_ker_src_fun

/-!
A60 dual: LI child + span-top child.
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
    LinearIndependent (Polynomial K) f ∧
      ⊤ ≤ Submodule.span (Polynomial K) (Set.range f) :=
  ⟨WeilConjectures.linearIndependent_of_on_range_ker_src_fun
      M d e bTgt v bKer f hmap hon hker,
    WeilConjectures.span_top_of_on_range_ker_src_fun
      M d e bTgt v bKer f hmap hon hker⟩
