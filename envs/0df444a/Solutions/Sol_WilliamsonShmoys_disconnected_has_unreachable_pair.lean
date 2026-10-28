-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_has_unreachable_pair
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:18:59.687774+00:00
-- url     : https://prove2.me/submissions/3f28ce07-53da-4cde-b3c6-218ab75c62f0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDisconnected : ¬ H.Connected),
    ∃ u v : V, ¬ H.Reachable u v) := by
  intro h
  obtain ⟨u, -⟩ := h (⊥ : SimpleGraph (Fin 0)) (fun hc => hc.nonempty.elim fun a => a.elim0)
  exact u.elim0
