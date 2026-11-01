-- Prove2me | solution 1 for WilliamsonShmoys.restrict_planar_drawing_to_induced_subgraph__p2m_ed6487b5_3fd2_47fb_a969_c3848ac24208_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:16:04.829414+00:00
-- url     : https://prove2.me/submissions/32d712b7-fe20-479e-9f88-14fe0c129b54

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (s : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (G.induce (s : Set V)) := by
  classical
  rcases hG with ⟨p, arc, hp, hEdge, hCross⟩
  refine ⟨(fun x : ↥s => p x.1), (fun (u v : ↥s) => arc u.1 v.1), ?_, ?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    exact hp hab
  · intro u v huv hadj
    have hadj' : G.Adj u.1 v.1 := hadj
    rcases hEdge u.1 v.1 (show u.1 < v.1 from huv) hadj' with
      ⟨hcont, hinj, hstart, hend, havoid⟩
    refine ⟨hcont, hinj, hstart, hend, ?_⟩
    intro t ht a
    exact havoid t ht a.1
  · intro u v x y huv hxy hadjuv hadjxy hne t ht r hr heq
    have hne' : (u.1, v.1) ≠ (x.1, y.1) := by
      intro hpair
      apply hne
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst hpair)
      · exact Subtype.ext (congrArg Prod.snd hpair)
    simpa using
      hCross u.1 v.1 x.1 y.1 huv hxy hadjuv hadjxy hne' t ht r hr heq