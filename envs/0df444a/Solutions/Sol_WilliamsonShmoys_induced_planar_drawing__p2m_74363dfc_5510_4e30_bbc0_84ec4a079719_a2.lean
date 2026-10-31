-- Prove2me | solution 1 for WilliamsonShmoys.induced_planar_drawing__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:16:51.936467+00:00
-- url     : https://prove2.me/submissions/2047b120-93ce-45f5-8792-1b4b7386a459

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (s : Finset V) :
    HasPlanarDrawingOn (K.induce (↑s : Set V)) := by
  rcases hK with ⟨p, arc, hp, hEdges, hCross⟩
  refine ⟨(fun u : (↑s : Set V) => p u.1),
    (fun u v t => arc u.1 v.1 t), ?_, ?_, ?_⟩
  · intro u v huv
    apply Subtype.ext
    apply hp
    exact huv
  · intro u v huv hadj
    change K.Adj u.1 v.1 at hadj
    rcases hEdges u.1 v.1 huv hadj with
      ⟨hcont, hinj, hstart, hend, hnoVertex⟩
    refine ⟨hcont, hinj, hstart, hend, ?_⟩
    intro t ht w
    exact hnoVertex t ht w.1
  · intro u v x y huv hxy hadjuv hadjxy hne t ht r hr heq
    change K.Adj u.1 v.1 at hadjuv
    change K.Adj x.1 y.1 at hadjxy
    have hne' : (u.1, v.1) ≠ (x.1, y.1) := by
      intro h
      apply hne
      rcases Prod.mk.inj h with ⟨hu, hv⟩
      exact Prod.ext (Subtype.ext hu) (Subtype.ext hv)
    exact hCross u.1 v.1 x.1 y.1 huv hxy hadjuv hadjxy hne' t ht r hr heq
