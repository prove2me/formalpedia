-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_induce_subset
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:46:17.160595+00:00
-- url     : https://prove2.me/submissions/146b2e66-546d-49af-a277-a93700b2885e

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {n : Nat} (G : SimpleGraph (Fin n))
    (hG : WilliamsonShmoys.HasPlanarDrawing G)
    (S : Set (Fin n)) [Fintype S] :
    WilliamsonShmoys.HasPlanarDrawingOn (G.induce S) := by 
  obtain ⟨p, arc, hp, harc, hcross⟩ := hG
  refine ⟨fun u => p u.val, fun u v => arc u.val v.val, hp.comp Subtype.val_injective, ?_, ?_⟩
  · intro u v huv hadj
    obtain ⟨h1, h2, h3, h4, h5⟩ := harc u.val v.val huv hadj
    exact ⟨h1, h2, h3, h4, fun t ht w => h5 t ht w.val⟩
  · intro u v x y huv hxy h1 h2 hne t ht s hs heq
    refine hcross u.val v.val x.val y.val huv hxy h1 h2 ?_ t ht s hs heq
    intro h
    apply hne
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
