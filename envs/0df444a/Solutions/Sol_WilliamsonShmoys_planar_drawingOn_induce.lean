-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_induce
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:03:03.709212+00:00
-- url     : https://prove2.me/submissions/b12b17f2-3988-4a56-b7b4-5c7de18db508

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (S : Finset V) :
    HasPlanarDrawingOn (K.induce (↑S : Set V)) := by
  rcases hK with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨fun u : (↑S : Set V) => p u.1,
    fun u v => arc u.1 v.1, ?_, ?_, ?_⟩
  · intro u v huv
    apply Subtype.ext
    exact hp huv
  · intro u v huv hadj
    have huv' : u.1 < v.1 := huv
    have hadj' : K.Adj u.1 v.1 := by simpa using hadj
    rcases hedge u.1 v.1 huv' hadj' with ⟨hc, hi, h0, h1, havoids⟩
    refine ⟨hc, hi, ?_, ?_, ?_⟩
    · simpa using h0
    · simpa using h1
    · intro t ht w
      exact havoids t ht w.1
  · intro u v x y huv hxy hadjuv hadjxy hneq t ht s hs heq
    have huv' : u.1 < v.1 := huv
    have hxy' : x.1 < y.1 := hxy
    have hadjuv' : K.Adj u.1 v.1 := by simpa using hadjuv
    have hadjxy' : K.Adj x.1 y.1 := by simpa using hadjxy
    have hneq' : (u.1, v.1) ≠ (x.1, y.1) := by
      intro h
      apply hneq
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst h
      · apply Subtype.ext
        exact congrArg Prod.snd h
    exact hcross u.1 v.1 x.1 y.1 huv' hxy' hadjuv' hadjxy' hneq' t ht s hs heq