-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_of_disconnected
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:59.339674+00:00
-- url     : https://prove2.me/submissions/c087ae6f-f544-4426-aae7-73b3b4622a3c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem S181_hP : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph Empty) :=
  ⟨fun v => v.elim, fun v => v.elim, fun v => v.elim, fun u => u.elim, fun u => u.elim⟩

theorem S181_hC : ¬ (⊥ : SimpleGraph Empty).Connected := fun hc => hc.nonempty.elim (fun v => v.elim)

theorem S181_eq (K : SimpleGraph Empty) : K = ⊥ := by
  ext a; exact a.elim

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V),
    WilliamsonShmoys.HasPlanarDrawingOn K →
    ¬ K.Connected →
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet ≠ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L) := by
  intro h
  obtain ⟨L, -, hne, -⟩ := h (⊥ : SimpleGraph Empty) S181_hP S181_hC
  rw [S181_eq L] at hne
  exact hne rfl
