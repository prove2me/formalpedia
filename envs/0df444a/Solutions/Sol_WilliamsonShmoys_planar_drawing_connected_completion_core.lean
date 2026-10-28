-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_completion_core
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T02:32:41.134574+00:00
-- url     : https://prove2.me/submissions/de7091c4-010f-4ec3-b289-18955a889f94

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
theorem fin0_draw (G : SimpleGraph (Fin 0)) : HasPlanarDrawingOn G :=
  ⟨fun w => w.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H), ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K) := by
  intro h
  obtain ⟨K, -, hc, -⟩ := h (⊥ : SimpleGraph (Fin 0)) (fin0_draw _)
  exact hc.nonempty.elim fun a => a.elim0
