-- Prove2me | solution 1 for WilliamsonShmoys.connected_edge_card_lower_bound__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:05:31.662394+00:00
-- url     : https://prove2.me/submissions/1cdb717c-1660-48cd-825b-488a62f71584

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) :
    Fintype.card V <= G.edgeFinset.card + 1 := by
  simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] using
    hconn.card_vert_le_card_edgeSet_add_one
