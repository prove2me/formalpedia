-- Prove2me | solution 1 for WilliamsonShmoys.connected_edge_count_lower_bound__p2m_2ca2cc35_45b9_454e_9480_d6c447ab0740_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:47:34.0412+00:00
-- url     : https://prove2.me/submissions/be85d994-b39f-42dd-85f1-7a7cc2553e92

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (hconn : H.Connected) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     Fintype.card V ≤ H.edgeFinset.card + 1) := by
  classical
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using
    hconn.card_vert_le_card_edgeSet_add_one