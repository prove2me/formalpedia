-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_connectedComponent__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:28:10.723318+00:00
-- url     : https://prove2.me/submissions/b5631e12-ea13-4a2d-bc89-d045fd396345

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (C : G.ConnectedComponent) [Fintype {v : V // v ∈ C.supp}] : WilliamsonShmoys.HasPlanarDrawingOn C.toSimpleGraph := by
  obtain ⟨p, arc, hp, ha, hc⟩ := hG
  refine ⟨fun v => p v.1, fun u v => arc u.1 v.1, hp.comp Subtype.val_injective, ?_, ?_⟩
  · intro u v huv hadj
    exact ha u.1 v.1 huv (by simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using hadj)
      |>.imp_right fun h => h.imp_right fun h => h.imp_right fun h => h.imp_right
        fun h t ht w => h t ht w.1
  · intro u v x y huv hxy h1 h2 hne
    refine hc u.1 v.1 x.1 y.1 huv hxy
      (by simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using h1)
      (by simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using h2) ?_
    intro h
    apply hne
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
