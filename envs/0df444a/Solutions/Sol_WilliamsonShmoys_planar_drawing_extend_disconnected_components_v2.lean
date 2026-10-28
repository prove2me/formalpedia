-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extend_disconnected_components_v2
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:19:03.854337+00:00
-- url     : https://prove2.me/submissions/40484d64-3a28-4877-a0e6-c3ab4bf8a6c0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem fin0_draw (G : SimpleGraph (Fin 0)) : HasPlanarDrawingOn G :=
  ⟨fun w => w.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : HasPlanarDrawingOn G)
    (hGdisc : ¬ G.Connected),
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      (∀ u v, H.Adj u v → G.Adj u v ∨ ¬ G.Reachable u v) ∧
      (∃ u v, H.Adj u v ∧ ¬ G.Reachable u v)) := by
  intro h
  obtain ⟨H, -, -, -, u, -⟩ := h (⊥ : SimpleGraph (Fin 0)) (fin0_draw _)
    (fun hc => hc.nonempty.elim fun a => a.elim0)
  exact u.elim0
