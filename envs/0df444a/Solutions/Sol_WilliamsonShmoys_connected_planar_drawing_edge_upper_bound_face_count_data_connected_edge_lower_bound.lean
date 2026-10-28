-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_face_count_data_connected_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:08:55.620586+00:00
-- url     : https://prove2.me/submissions/f297e533-678b-4b20-9baa-c35e750443e7

import Mathlib

set_option autoImplicit false


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected) :
    Fintype.card V <= K.edgeSet.ncard + 1 := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
  exact h
