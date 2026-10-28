-- Prove2me | solution 1 for WilliamsonShmoys.connected_edgeLower
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:41:23.271959+00:00
-- url     : https://prove2.me/submissions/a26e4f15-6670-42bc-884f-9f3956f185b7

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected) :
    Fintype.card V <= G.edgeSet.ncard + 1 := by
  simpa [Nat.card_eq_fintype_card] using
    (SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one hconn)