-- Prove2me | solution 1 for WilliamsonShmoys.connected_graph_edge_count_lower_bound__p2m_367e7ff6_f47c_4801_a657_f77b95acb1d0_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:04:52.035119+00:00
-- url     : https://prove2.me/submissions/f8c855a5-4b0c-456b-842e-46114066aad6

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (hConn : H.Connected) :
    Fintype.card V ≤ H.edgeSet.ncard + 1 := by
  simpa only [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
    hConn.card_vert_le_card_edgeSet_add_one