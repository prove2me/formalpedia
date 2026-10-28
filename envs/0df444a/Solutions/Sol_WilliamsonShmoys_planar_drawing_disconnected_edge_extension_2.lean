-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_disconnected_edge_extension
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:53:20.052606+00:00
-- url     : https://prove2.me/submissions/e67e73a8-16ab-4ad2-a3af-79b9a178108c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V),
    WilliamsonShmoys.HasPlanarDrawingOn H →
    ¬ H.Connected →
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ¬ K ≤ H) := by
  intro h
  have hP : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph Empty) :=
    ⟨fun v => v.elim, fun v => v.elim, fun v => v.elim, fun u => u.elim, fun u => u.elim⟩
  have hC : ¬ (⊥ : SimpleGraph Empty).Connected := fun hc => hc.nonempty.elim (fun v => v.elim)
  obtain ⟨K, -, -, hK⟩ := h (⊥ : SimpleGraph Empty) hP hC
  exact hK fun u => u.elim
