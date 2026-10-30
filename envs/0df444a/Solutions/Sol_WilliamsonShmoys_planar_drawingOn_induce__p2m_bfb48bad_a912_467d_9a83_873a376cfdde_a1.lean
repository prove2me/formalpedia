-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_induce__p2m_bfb48bad_a912_467d_9a83_873a376cfdde_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:51:27.881066+00:00
-- url     : https://prove2.me/submissions/850d947d-da83-4682-8fd3-1200819b263d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (s : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (H.induce (↑s : Set V)) := by
  rcases hH with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨(fun v : (↑s : Set V) => p v.1),
    (fun u v t => arc u.1 v.1 t), ?_, ?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    exact hp hab
  · intro u v huv hadj
    have huv' : u.1 < v.1 := huv
    change H.Adj u.1 v.1 at hadj
    rcases hedge u.1 v.1 huv' hadj with ⟨hcont, hinj, hzero, hone, havoid⟩
    refine ⟨hcont, hinj, hzero, hone, ?_⟩
    intro t ht w
    exact havoid t ht w.1
  · intro u v x y huv hxy hadj1 hadj2 hpair t ht r hr heq
    have huv' : u.1 < v.1 := huv
    have hxy' : x.1 < y.1 := hxy
    change H.Adj u.1 v.1 at hadj1
    change H.Adj x.1 y.1 at hadj2
    have hpair' : (u.1, v.1) ≠ (x.1, y.1) := by
      intro heq'
      apply hpair
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst heq')
      · exact Subtype.ext (congrArg Prod.snd heq')
    exact hcross u.1 v.1 x.1 y.1 huv' hxy' hadj1 hadj2 hpair' t ht r hr heq