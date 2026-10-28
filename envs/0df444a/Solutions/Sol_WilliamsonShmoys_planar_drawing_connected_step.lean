-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_step
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:34:27.765179+00:00
-- url     : https://prove2.me/submissions/05d9a660-6103-45ea-8b38-8c6d685d6842

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected),
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v, ¬ G.Reachable u v ∧ H.Adj u v) := by
  intro h
  have hd : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun v => v.elim0, fun u => u.elim0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  obtain ⟨H, -, -, u, -⟩ := h (⊥ : SimpleGraph (Fin 0)) hd (fun hc => hc.nonempty.elim fun v => v.elim0)
  exact u.elim0
