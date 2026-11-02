-- Prove2me | solution 1 for WilliamsonShmoys.connected_graph_card_le_edge_ncard_add_one__p2m_c14927fd_3bb2_4aa2_8e62_690259e960a9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:56:01.701557+00:00
-- url     : https://prove2.me/submissions/7923a03d-bd1a-4983-8264-d33710dd42b7

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V) (hconn : K.Connected) :
    Fintype.card V ≤ K.edgeSet.ncard + 1 := by
  simpa only [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
    SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one hconn