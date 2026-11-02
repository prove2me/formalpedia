-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_induce__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:38:13.585011+00:00
-- url     : https://prove2.me/submissions/0b9dd257-8bce-4ece-9006-d94ee983376d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (s : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (G.induce (↑s : Set V)) := by
  classical
  rcases hG with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨(fun u : {x // x ∈ (↑s : Set V)} => p u.1),
    (fun u v t => arc u.1 v.1 t), ?_, ?_, ?_⟩
  · intro u v huv
    apply Subtype.ext
    exact hp huv
  · intro u v huv hadj
    change u.1 < v.1 at huv
    change G.Adj u.1 v.1 at hadj
    obtain ⟨hcont, hinj, hzero, hone, havoid⟩ := hedge u.1 v.1 huv hadj
    refine ⟨hcont, hinj, hzero, hone, ?_⟩
    intro t ht w heq
    exact havoid t ht w (by simpa using heq)
  · intro u v x y huv hxy hadjuv hadjxy hne t ht r hr heq
    change u.1 < v.1 at huv
    change x.1 < y.1 at hxy
    change G.Adj u.1 v.1 at hadjuv
    change G.Adj x.1 y.1 at hadjxy
    have hne' : (u.1, v.1) ≠ (x.1, y.1) := by
      intro heq'
      apply hne
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun q : V × V => q.1) heq'
      · apply Subtype.ext
        exact congrArg (fun q : V × V => q.2) heq'
    have hout := hcross u.1 v.1 x.1 y.1 huv hxy hadjuv hadjxy hne' t ht r hr
    simpa using hout (by simpa using heq)