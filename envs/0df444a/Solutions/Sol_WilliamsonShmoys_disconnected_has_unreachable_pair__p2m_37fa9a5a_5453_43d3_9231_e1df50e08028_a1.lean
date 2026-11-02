-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_37fa9a5a_5453_43d3_9231_e1df50e08028_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:24:58.742116+00:00
-- url     : https://prove2.me/submissions/c09a75e5-97c9-423b-addc-0ae03929ec90

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ u v : V, ¬ K.Reachable u v := by
  classical
  by_contra hpair
  have hreach : ∀ u v : V, K.Reachable u v := by
    intro u v
    by_contra huv
    exact hpair ⟨u, v, huv⟩
  have hnonempty : Nonempty V := by
    apply Fintype.card_pos_iff.mp
    omega
  apply hDisconnected
  rw [SimpleGraph.connected_iff]
  exact ⟨hreach, hnonempty⟩