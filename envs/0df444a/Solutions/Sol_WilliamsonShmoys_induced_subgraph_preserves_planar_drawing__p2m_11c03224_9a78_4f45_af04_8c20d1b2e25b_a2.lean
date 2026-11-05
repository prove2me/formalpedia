-- Prove2me | solution 1 for WilliamsonShmoys.induced_subgraph_preserves_planar_drawing__p2m_11c03224_9a78_4f45_af04_8c20d1b2e25b_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:41:08.219554+00:00
-- url     : https://prove2.me/submissions/0626793c-0654-48d9-bd34-ffd858f374de

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (s : Finset V) :
    HasPlanarDrawingOn (L.induce (s : Set V)) := by
  classical
  rcases hL with ⟨p, arc, hp, hsingle, hpair⟩
  refine ⟨(fun u : (s : Set V) => p u.1),
    (fun (u v : (s : Set V)) t => arc u.1 v.1 t), ?_, ?_, ?_⟩
  · intro u v hEq
    exact Subtype.ext (hp hEq)
  · intro u v huv huv_adj
    have huv' : u.1 < v.1 := by simpa using huv
    have hadj : L.Adj u.1 v.1 := by simpa using huv_adj
    rcases hsingle u.1 v.1 huv' hadj with ⟨hc, hi, h0, h1, hav⟩
    refine ⟨hc, hi, h0, h1, ?_⟩
    intro t ht w
    exact hav t ht w.1
  · intro u v x y huv hxy huv_adj hxy_adj hne t ht s' hs' heq
    have huv' : u.1 < v.1 := by simpa using huv
    have hxy' : x.1 < y.1 := by simpa using hxy
    have hadj : L.Adj u.1 v.1 := by simpa using huv_adj
    have hadj' : L.Adj x.1 y.1 := by simpa using hxy_adj
    have hne' : (u.1, v.1) ≠ (x.1, y.1) := by
      intro h
      apply hne
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h))
    exact hpair u.1 v.1 x.1 y.1 huv' hxy' hadj hadj' hne' t ht s' hs' heq
