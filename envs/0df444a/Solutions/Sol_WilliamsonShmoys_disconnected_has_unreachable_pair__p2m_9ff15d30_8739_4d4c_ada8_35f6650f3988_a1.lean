-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_9ff15d30_8739_4d4c_ada8_35f6650f3988_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:21:16.995127+00:00
-- url     : https://prove2.me/submissions/c22340de-0258-4c92-86f5-fdd01b60cfe1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V), ¬ K.Connected → ∃ u v : V, ¬ K.Reachable u v) := by
  intro h
  let K : SimpleGraph Empty := ⊤
  have hnot : ¬ K.Connected := by
    simp [K, SimpleGraph.connected_iff]
  have hex : ∃ u v : Empty, ¬ K.Reachable u v := h (V := Empty) K hnot
  rcases hex with ⟨u, v, _⟩
  cases u