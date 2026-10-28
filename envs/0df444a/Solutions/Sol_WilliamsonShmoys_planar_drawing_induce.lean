-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_induce
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:16:16.528342+00:00
-- url     : https://prove2.me/submissions/f77ac9f1-b179-454b-bc39-e0c1cc38582e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (S : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (H.induce (↑S : Set V)) := by
  rcases hH with ⟨p, arc, hp_inj, hp_edges, hp_crossings⟩
  refine ⟨(fun x : {v : V // v ∈ S} => p x.1),
    (fun x y t => arc x.1 y.1 t), ?_, ?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    exact hp_inj hxy
  · intro u v huv hadj
    have huv' : u.1 < v.1 := huv
    have hadj' : H.Adj u.1 v.1 := hadj
    rcases hp_edges u.1 v.1 huv' hadj' with
      ⟨hcont, hinj, hzero, hone, havoid⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa using hcont
    · simpa using hinj
    · simpa using hzero
    · simpa using hone
    · intro t ht w
      exact havoid t ht w.1
  · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
    have huv' : u.1 < v.1 := huv
    have hxy' : x.1 < y.1 := hxy
    have hadj₁' : H.Adj u.1 v.1 := hadj₁
    have hadj₂' : H.Adj x.1 y.1 := hadj₂
    have hne' : (u.1, v.1) ≠ (x.1, y.1) := by
      intro h
      apply hne
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h))
    simpa using
      hp_crossings u.1 v.1 x.1 y.1 huv' hxy' hadj₁' hadj₂' hne' t ht s hs heq