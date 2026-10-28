-- Prove2me | solution 1 for WilliamsonShmoys.connected_card_le_edge_ncard_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:23:32.866318+00:00
-- url     : https://prove2.me/submissions/4a62fde4-6e2b-464f-9217-f731354dc45c

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hconn : L.Connected) :
    Fintype.card V ≤ L.edgeSet.ncard + 1 := by
  simpa [Nat.card_eq_fintype_card, Set.ncard_eq_toFinset_card'] using
    hconn.card_vert_le_card_edgeSet_add_one