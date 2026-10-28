-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_v2
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:38:14.065097+00:00
-- url     : https://prove2.me/submissions/ccdb0a5c-3094-4e33-b4ba-1c85477cd1a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem fin0_draw (G : SimpleGraph (Fin 0)) : HasPlanarDrawingOn G :=
  ⟨fun w => w.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y),
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧
      Y.edgeSet.ncard ≤ Z.edgeSet.ncard ∧
      Z.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z) := by
  intro h
  obtain ⟨Z, -, -, hZ, -⟩ := h (⊥ : SimpleGraph (Fin 0)) (fin0_draw _)
  exact (hZ.nonempty.elim fun a => a.elim0)
