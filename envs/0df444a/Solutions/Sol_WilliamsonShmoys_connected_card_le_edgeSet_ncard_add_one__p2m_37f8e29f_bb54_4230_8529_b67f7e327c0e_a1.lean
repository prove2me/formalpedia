-- Prove2me | solution 1 for WilliamsonShmoys.connected_card_le_edgeSet_ncard_add_one__p2m_37f8e29f_bb54_4230_8529_b67f7e327c0e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:25:35.713354+00:00
-- url     : https://prove2.me/submissions/933b4ee0-9995-4be7-81ac-a6e6a053d294

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hconn : G.Connected) :
    Fintype.card V ≤ G.edgeSet.ncard + 1 := by
  simpa only [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
    (SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one hconn)