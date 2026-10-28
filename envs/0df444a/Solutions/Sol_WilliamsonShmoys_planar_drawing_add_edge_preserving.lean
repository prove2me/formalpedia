-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_preserving
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:34:20.402329+00:00
-- url     : https://prove2.me/submissions/09a23e77-6e84-4893-bd74-98cbb929e7f6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hGdisc : ¬ G.Connected),
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ u v, H.Adj u v → G.Adj u v ∨ ¬ G.Reachable u v) ∧
      (∃ u v, H.Adj u v ∧ ¬ G.Reachable u v)) := by
  intro h
  have hd : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun v => v.elim0, fun u => u.elim0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  obtain ⟨H, -, -, -, u, -⟩ := h (⊥ : SimpleGraph (Fin 0)) hd (fun hc => hc.nonempty.elim fun v => v.elim0)
  exact u.elim0
