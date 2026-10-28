-- Prove2me | solution 1 for WilliamsonShmoys.drawingOn_restrict_induce_282b0fbb
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:12:54.534753+00:00
-- url     : https://prove2.me/submissions/73655542-208e-48a5-b3b2-933777593a1b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (S : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (L.induce S) := by
  obtain ⟨p, arc, hp, harc, hcross⟩ := hL
  refine ⟨fun w => p w.1, fun u v => arc u.1 v.1, hp.comp Subtype.val_injective, ?_, ?_⟩
  · intro u v huv hadj
    obtain ⟨h1, h2, h3, h4, h5⟩ := harc u.1 v.1 huv hadj
    exact ⟨h1, h2, h3, h4, fun t ht w => h5 t ht w.1⟩
  · intro u v x y huv hxy hadj1 hadj2 hne t ht s hs heq
    refine hcross u.1 v.1 x.1 y.1 huv hxy hadj1 hadj2 ?_ t ht s hs heq
    intro h
    apply hne
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
