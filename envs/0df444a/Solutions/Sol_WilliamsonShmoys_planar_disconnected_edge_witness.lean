-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_edge_witness
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:53:12.944611+00:00
-- url     : https://prove2.me/submissions/1a12c6a1-0a4f-4485-b4bf-f903aef71aaf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V),
    WilliamsonShmoys.HasPlanarDrawingOn H →
    ¬ H.Connected →
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ u v : V, ¬ H.Adj u v ∧ K.Adj u v) := by
  intro h
  have hP : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph Empty) :=
    ⟨fun v => v.elim, fun v => v.elim, fun v => v.elim, fun u => u.elim, fun u => u.elim⟩
  have hC : ¬ (⊥ : SimpleGraph Empty).Connected := fun hc => hc.nonempty.elim (fun v => v.elim)
  obtain ⟨K, -, -, u, -⟩ := h (⊥ : SimpleGraph Empty) hP hC
  exact u.elim

