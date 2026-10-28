-- Prove2me | solution 1 for WilliamsonShmoys.exists_not_reachable_of_not_connected
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:00:39.406696+00:00
-- url     : https://prove2.me/submissions/4d8ba95e-9180-4095-9fab-d1487b80374c

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V) (hDisconnected : ¬ G.Connected),
      ∃ u v : V, ¬ G.Reachable u v) := by
  intro h
  let G : SimpleGraph (Fin 0) := ⊥
  have hDisconnected : ¬ G.Connected := by
    intro hc
    exact Fin.elim0 (Classical.choice hc.nonempty)
  obtain ⟨u, v, _⟩ := h (V := Fin 0) G hDisconnected
  exact Fin.elim0 u