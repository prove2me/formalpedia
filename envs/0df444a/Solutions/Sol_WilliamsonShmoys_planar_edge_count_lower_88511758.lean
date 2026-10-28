-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_lower_88511758
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:45:07.117813+00:00
-- url     : https://prove2.me/submissions/6e7bd907-d33f-446c-94a7-6544e3ed6484

import Mathlib
set_option autoImplicit false
theorem solution {V : Type} [Fintype V] (H : SimpleGraph V) (hconn : H.Connected) : Fintype.card V ≤ H.edgeSet.ncard + 1 := by
  classical
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (H.edgeSet).ncard = Nat.card H.edgeSet := (Nat.card_coe_set_eq _).symm
  omega
