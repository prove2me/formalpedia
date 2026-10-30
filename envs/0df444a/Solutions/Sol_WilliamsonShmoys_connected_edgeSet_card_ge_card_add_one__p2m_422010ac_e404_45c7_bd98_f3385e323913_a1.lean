-- Prove2me | solution 1 for WilliamsonShmoys.connected_edgeSet_card_ge_card_add_one__p2m_422010ac_e404_45c7_bd98_f3385e323913_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:48:04.566617+00:00
-- url     : https://prove2.me/submissions/71f25135-d4a2-4e9d-9112-4eae97d4a44a

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (H : SimpleGraph V) :
    H.Connected → Fintype.card V ≤ H.edgeSet.ncard + 1 := by
  intro h
  simpa only [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
    (SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one h)