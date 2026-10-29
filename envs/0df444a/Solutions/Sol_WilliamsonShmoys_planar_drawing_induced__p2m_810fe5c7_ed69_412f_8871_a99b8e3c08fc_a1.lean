-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_induced__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:42:40.319848+00:00
-- url     : https://prove2.me/submissions/3650a6cd-5cfa-46a2-ab29-97f60f3e3b17

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (S : Finset V) :
    HasPlanarDrawingOn (G.induce (S : Set V)) := by
  classical
  rcases hG with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨(fun x : S => p x.1), (fun x y t => arc x.1 y.1 t), ?_, ?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    exact hp hxy
  · intro u v huv hadj
    change u.1 < v.1 at huv
    change G.Adj u.1 v.1 at hadj
    rcases hedge u.1 v.1 huv hadj with ⟨hc, hi, h0, h1, havoid⟩
    refine ⟨hc, hi, h0, h1, ?_⟩
    intro t ht w
    exact havoid t ht w.1
  · intro u v x y huv hxy hadjuv hadjxy hne t ht s hs heq
    change u.1 < v.1 at huv
    change x.1 < y.1 at hxy
    change G.Adj u.1 v.1 at hadjuv
    change G.Adj x.1 y.1 at hadjxy
    apply hcross u.1 v.1 x.1 y.1 huv hxy hadjuv hadjxy
    · intro he
      apply hne
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst he
      · apply Subtype.ext
        exact congrArg Prod.snd he
    · exact ht
    · exact hs
    · exact heq