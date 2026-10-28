-- Prove2me | solution 2 for WilliamsonShmoys.drawable_disconnected_has_drawable_extension
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T04:07:36.807861+00:00
-- url     : https://prove2.me/submissions/28e39229-c45e-4bdf-8291-a8fa56a2df6b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys
theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hdisc : ¬ Q.Connected),
    ∃ M : SimpleGraph V,
      Q ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ¬ M ≤ Q) := by
  intro h
  have hd : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun v => v.elim0, fun u => u.elim0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  have hnc : ¬ (⊥ : SimpleGraph (Fin 0)).Connected := fun hc => hc.nonempty.elim fun v => v.elim0
  obtain ⟨M, -, -, hM⟩ := h (⊥ : SimpleGraph (Fin 0)) hd hnc
  exact hM fun u => u.elim0
