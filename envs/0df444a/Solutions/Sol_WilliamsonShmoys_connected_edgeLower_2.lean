-- Prove2me | solution 2 for WilliamsonShmoys.connected_edgeLower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:41:54.611833+00:00
-- url     : https://prove2.me/submissions/0ae85c5e-0554-46cc-8465-4d84e4faf355

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected) :
    Fintype.card V <= G.edgeSet.ncard + 1 := by
  classical
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (G.edgeSet).ncard = Nat.card G.edgeSet := (Nat.card_coe_set_eq _).symm
  omega
