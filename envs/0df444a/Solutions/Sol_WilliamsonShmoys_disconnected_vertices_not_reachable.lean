-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_vertices_not_reachable
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:38:36.891584+00:00
-- url     : https://prove2.me/submissions/204b8061-cd28-4669-b0ac-cbb36e3107b7

import Mathlib
set_option autoImplicit false
theorem solution : ¬ (∀ {V : Type} [Fintype V] (H : SimpleGraph V)
    (hNotConnected : ¬ H.Connected),
    ∃ u v : V, ¬ H.Reachable u v) := by
  intro h
  obtain ⟨u, -⟩ := h (⊥ : SimpleGraph (Fin 0)) (fun hc => hc.nonempty.elim fun a => a.elim0)
  exact u.elim0
