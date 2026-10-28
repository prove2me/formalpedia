-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_restrict_induced
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:05:48.265225+00:00
-- url     : https://prove2.me/submissions/e70f87c2-fba2-45fa-bb05-0b45d111021a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (S : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (G.induce (↑S : Set V)) := by
  obtain ⟨p, arc, hp, harc, hcross⟩ := hdraw
  refine ⟨fun w => p w.1, fun u v => arc u.1 v.1, hp.comp Subtype.val_injective, ?_, ?_⟩
  · intro u v huv hadj
    obtain ⟨h1, h2, h3, h4, h5⟩ := harc u.1 v.1 huv hadj
    exact ⟨h1, h2, h3, h4, fun t ht w => h5 t ht w.1⟩
  · intro u v x y huv hxy h1 h2 hne t ht s hs heq
    refine hcross u.1 v.1 x.1 y.1 huv hxy h1 h2 ?_ t ht s hs heq
    intro h
    apply hne
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
