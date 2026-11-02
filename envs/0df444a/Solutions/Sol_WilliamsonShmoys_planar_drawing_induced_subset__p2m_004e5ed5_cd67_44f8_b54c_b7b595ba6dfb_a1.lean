-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_induced_subset__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:53:20.204542+00:00
-- url     : https://prove2.me/submissions/9025c4fa-efa8-49a3-aae3-1c28ee678cb6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U) (S : Finset V) :
    HasPlanarDrawingOn (U.induce (↑S : Set V)) := by
  rcases hU with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨(fun x => p x.1), (fun x y t => arc x.1 y.1 t), ?_, ?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    exact hp hxy
  · intro u v huv hadj
    have huv' : u.1 < v.1 := huv
    have hadj' : U.Adj u.1 v.1 := by
      simpa using hadj
    rcases hedge u.1 v.1 huv' hadj' with
      ⟨hcont, hinj, hzero, hone, hvertex⟩
    refine ⟨hcont, hinj, ?_, ?_, ?_⟩
    · simpa using hzero
    · simpa using hone
    · intro t ht w
      simpa using hvertex t ht w.1
  · intro u v x y huv hxy huvAdj hxyAdj hne t ht s hs heq
    have huv' : u.1 < v.1 := huv
    have hxy' : x.1 < y.1 := hxy
    have huvAdj' : U.Adj u.1 v.1 := by
      simpa using huvAdj
    have hxyAdj' : U.Adj x.1 y.1 := by
      simpa using hxyAdj
    have hne' : (u.1, v.1) ≠ (x.1, y.1) := by
      intro h
      apply hne
      exact Prod.ext
        (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h))
    exact hcross u.1 v.1 x.1 y.1 huv' hxy' huvAdj' hxyAdj' hne' t ht s hs heq