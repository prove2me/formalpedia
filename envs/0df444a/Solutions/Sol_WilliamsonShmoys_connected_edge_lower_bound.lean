-- Prove2me | solution 1 for WilliamsonShmoys.connected_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:48:52.913037+00:00
-- url     : https://prove2.me/submissions/105795cd-dc79-454f-a164-8c74a75332bf

import Mathlib

set_option autoImplicit false


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected) :
    Fintype.card V <= K.edgeSet.ncard + 1 := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
  exact h
