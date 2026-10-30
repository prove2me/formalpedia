-- Prove2me | solution 1 for WilliamsonShmoys.connected_edge_count_lower_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:12:15.667093+00:00
-- url     : https://prove2.me/submissions/087b384a-eb5e-4a86-98cf-c724a486d0e1

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (H : SimpleGraph V) (hconn : H.Connected) :
    Fintype.card V ≤ H.edgeSet.ncard + 1 := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  simpa [Nat.card_eq_fintype_card, Set.ncard_eq_toFinset_card] using h