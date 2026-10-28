-- Prove2me | solution 1 for WilliamsonShmoys.drawable_disconnected_has_drawable_extension
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T04:07:01.685354+00:00
-- url     : https://prove2.me/submissions/2e6afac8-e734-49c6-a9a1-b45f6df88c4d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem fin0_draw (G : SimpleGraph (Fin 0)) : HasPlanarDrawingOn G :=
  ⟨fun w => w.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hdisc : ¬ Q.Connected),
    ∃ M : SimpleGraph V,
      Q ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ¬ M ≤ Q) := by
  intro h
  obtain ⟨M, -, -, hM⟩ := h (⊥ : SimpleGraph (Fin 0)) (fin0_draw _)
    (fun hc => hc.nonempty.elim fun a => a.elim0)
  exact hM (fun a => a.elim0)
