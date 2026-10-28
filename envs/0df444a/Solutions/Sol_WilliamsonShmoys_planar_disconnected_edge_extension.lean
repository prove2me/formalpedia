-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_edge_extension
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:24:10.738496+00:00
-- url     : https://prove2.me/submissions/6216c6b5-5940-4d24-9c57-8df464173685

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
theorem fin0_draw (G : SimpleGraph (Fin 0)) : HasPlanarDrawingOn G :=
  ⟨fun w => w.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hDisconnected : ¬ K.Connected), ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ K.edgeSet.ncard < H.edgeSet.ncard) := by
  intro h
  obtain ⟨H, -, -, hlt⟩ := h (⊥ : SimpleGraph (Fin 0)) (fin0_draw _)
    (fun hc => hc.nonempty.elim fun a => a.elim0)
  have : H.edgeSet = ∅ := Set.eq_empty_of_forall_notMem fun e => e.ind fun a _ => a.elim0
  simp [this] at hlt
