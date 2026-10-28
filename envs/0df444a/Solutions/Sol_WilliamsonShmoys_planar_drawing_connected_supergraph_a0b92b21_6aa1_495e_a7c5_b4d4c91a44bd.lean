-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T02:32:56.305763+00:00
-- url     : https://prove2.me/submissions/85ab55fd-0202-4df7-ac5f-2f6e7b025f0f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
theorem fin0_draw (G : SimpleGraph (Fin 0)) : HasPlanarDrawingOn G :=
  ⟨fun w => w.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H), ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K) := by
  intro h
  obtain ⟨K, -, hc, -⟩ := h (⊥ : SimpleGraph (Fin 0)) (fin0_draw _)
  exact hc.nonempty.elim fun a => a.elim0
