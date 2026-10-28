-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_restrict_induced
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:17:45.841672+00:00
-- url     : https://prove2.me/submissions/a061a659-9099-449f-80bc-39c844a73491

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (W : Set V) (hFW : Fintype W) :
    WilliamsonShmoys.HasPlanarDrawingOn (K.induce W) := by
  letI : Fintype W := hFW
  rcases hdraw with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨(fun w : W => p w.1), (fun u v t => arc u.1 v.1 t), ?_, ?_, ?_⟩
  · intro u v huv
    apply Subtype.ext
    exact hp huv
  · intro u v huv hadj
    change u.1 < v.1 at huv
    change K.Adj u.1 v.1 at hadj
    obtain ⟨hcont, hinj, hzero, hone, havoid⟩ := hedge u.1 v.1 huv hadj
    refine ⟨hcont, hinj, hzero, hone, ?_⟩
    intro t ht w
    exact havoid t ht w.1
  · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
    change u.1 < v.1 at huv
    change x.1 < y.1 at hxy
    change K.Adj u.1 v.1 at hadj
    change K.Adj x.1 y.1 at hadj'
    have hne' : (u.1, v.1) ≠ (x.1, y.1) := by
      intro hval
      apply hne
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst hval
      · apply Subtype.ext
        exact congrArg Prod.snd hval
    exact hcross u.1 v.1 x.1 y.1 huv hxy hadj hadj' hne' t ht s hs heq