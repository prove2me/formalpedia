-- Prove2me | solution 1 for WilliamsonShmoys.induced_planar_drawing_restrict__p2m_5617b1c6_c5d8_46d6_8dd2_454c2352497f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:12:14.477193+00:00
-- url     : https://prove2.me/submissions/8bee0259-4a78-4ef3-bc83-71c834584300

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hdraw : HasPlanarDrawingOn M) (C : Finset V) :
    HasPlanarDrawingOn (M.induce (C : Set V)) := by
  rcases hdraw with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨(fun v : {x // x ∈ C} => p v.1),
    (fun u v t => arc u.1 v.1 t), ?_, ?_, ?_⟩
  · intro u v huv
    apply Subtype.ext
    exact hp huv
  · intro u v huv hadj
    have huv' : u.1 < v.1 := huv
    change M.Adj u.1 v.1 at hadj
    rcases hedge u.1 v.1 huv' hadj with
      ⟨hcont, hinj, hstart, hend, havoid⟩
    exact ⟨hcont, hinj, hstart, hend, fun t ht w => havoid t ht w.1⟩
  · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
    have huv' : u.1 < v.1 := huv
    have hxy' : x.1 < y.1 := hxy
    change M.Adj u.1 v.1 at hadj₁
    change M.Adj x.1 y.1 at hadj₂
    have hne' : (u.1, v.1) ≠ (x.1, y.1) := by
      intro heq'
      apply hne
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst heq')
      · exact Subtype.ext (congrArg Prod.snd heq')
    exact hcross u.1 v.1 x.1 y.1 huv' hxy' hadj₁ hadj₂ hne' t ht s hs heq