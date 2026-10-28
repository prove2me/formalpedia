-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_finset_induce_b095f50e
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:51:48.482054+00:00
-- url     : https://prove2.me/submissions/352bbaa5-d587-4d84-8c52-ec571d2b0712

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn W)
    (S : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (W.induce (↑S : Set V)) := by
  obtain ⟨p, arc, hinj, hedge, hcross⟩ := hDrawing
  refine ⟨fun x => p x.1, fun x y => arc x.1 y.1, ?_, ?_, ?_⟩
  · intro a b hab
    exact Subtype.ext (hinj hab)
  · intro u v huv hadj
    have hadj' : W.Adj u.1 v.1 := by simpa using hadj
    have huv' : u.1 < v.1 := huv
    obtain ⟨h1, h2, h3, h4, h5⟩ := hedge u.1 v.1 huv' hadj'
    refine ⟨h1, h2, h3, h4, ?_⟩
    intro t ht w
    exact h5 t ht w.1
  · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
    have hadj1 : W.Adj u.1 v.1 := by simpa using hadj
    have hadj2 : W.Adj x.1 y.1 := by simpa using hadj'
    have hne' : (u.1, v.1) ≠ (x.1, y.1) := by
      intro h
      apply hne
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
    exact hcross u.1 v.1 x.1 y.1 huv hxy hadj1 hadj2 hne' t ht s hs heq
