-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_between_components__p2m_343e7634_bf89_4d0d_a54b_557d3af37c62_a1
-- status  : ACCEPTED   (disprove)
-- author  : @もち
-- created : 2026-11-24T04:52:27.533805+00:00
-- url     : https://prove2.me/submissions/56b1a2f4-23cb-4cc0-b7a0-18d5b31bc19e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V)
      (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
      (hDisconnected : ¬ G.Connected),
      ∃ H : SimpleGraph V,
        G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v) := by
  intro h
  have hDraw : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun x => x.elim0, fun _ _ _ => 0, fun x => x.elim0,
      fun u => u.elim0, fun u => u.elim0⟩
  have hnc : ¬ (⊥ : SimpleGraph (Fin 0)).Connected := fun hc => by
    obtain ⟨x⟩ := hc.nonempty
    exact x.elim0
  obtain ⟨H, -, -, u, -, -⟩ := h (⊥ : SimpleGraph (Fin 0)) hDraw hnc
  exact u.elim0
