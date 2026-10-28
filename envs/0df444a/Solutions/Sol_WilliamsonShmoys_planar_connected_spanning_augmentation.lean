-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_spanning_augmentation
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:19:10.844582+00:00
-- url     : https://prove2.me/submissions/cc8aa27e-93da-4b02-9029-1d593eab0962

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem fin0_draw (G : SimpleGraph (Fin 0)) : HasPlanarDrawingOn G :=
  ⟨fun w => w.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hnotconn : ¬ T.Connected),
    ∃ H : SimpleGraph V, T ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H) := by
  intro h
  obtain ⟨H, -, hc, -⟩ := h (⊥ : SimpleGraph (Fin 0)) (fin0_draw _)
    (fun hc => hc.nonempty.elim fun a => a.elim0)
  exact hc.nonempty.elim fun a => a.elim0
