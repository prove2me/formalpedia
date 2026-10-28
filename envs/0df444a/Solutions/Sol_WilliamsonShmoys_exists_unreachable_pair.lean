-- Prove2me | solution 1 for WilliamsonShmoys.exists_unreachable_pair
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:14:17.0494+00:00
-- url     : https://prove2.me/submissions/95346d11-26bf-4329-8860-2647863bb0b4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hnotConnected : ¬ P.Connected),
    ∃ u v : V, u ≠ v ∧ ¬ P.Reachable u v) := by
  intro h
  obtain ⟨u, -⟩ := h (⊥ : SimpleGraph (Fin 0)) (fun hc => hc.nonempty.elim fun a => a.elim0)
  exact u.elim0
