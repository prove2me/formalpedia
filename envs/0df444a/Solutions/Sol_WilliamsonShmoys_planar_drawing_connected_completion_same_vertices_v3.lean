-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_completion_same_vertices_v3
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T03:48:36.755097+00:00
-- url     : https://prove2.me/submissions/53189652-8353-4aa6-84b1-e377784b1929

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem fin0_draw (G : SimpleGraph (Fin 0)) : HasPlanarDrawingOn G :=
  ⟨fun w => w.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H),
    ∃ J : SimpleGraph V, H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧ J.Connected) := by
  intro h
  obtain ⟨J, -, -, hJ⟩ := h (⊥ : SimpleGraph (Fin 0)) (fin0_draw _)
  exact (hJ.nonempty.elim fun a => a.elim0)
