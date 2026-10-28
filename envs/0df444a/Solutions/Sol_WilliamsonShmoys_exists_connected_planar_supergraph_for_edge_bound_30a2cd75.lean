-- Prove2me | solution 1 for WilliamsonShmoys.exists_connected_planar_supergraph_for_edge_bound_30a2cd75
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:40:15.19239+00:00
-- url     : https://prove2.me/submissions/04750a19-2d9b-4899-9b0d-2538f8e4edb7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem fin0_draw (G : SimpleGraph (Fin 0)) : HasPlanarDrawingOn G :=
  ⟨fun w => w.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G), ∃ H : SimpleGraph V, G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected) := by
  intro h
  obtain ⟨H, -, -, hc⟩ := h (⊥ : SimpleGraph (Fin 0)) (fin0_draw _)
  exact hc.nonempty.elim fun a => a.elim0
