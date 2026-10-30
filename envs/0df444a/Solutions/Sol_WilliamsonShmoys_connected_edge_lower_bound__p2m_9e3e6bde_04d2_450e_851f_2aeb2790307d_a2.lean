-- Prove2me | solution 1 for WilliamsonShmoys_connected_edge_lower_bound__p2m_9e3e6bde_04d2_450e_851f_2aeb2790307d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:39:06.388493+00:00
-- url     : https://prove2.me/submissions/41642378-b52e-41a1-8790-658210ec565f

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (hConnected : G.Connected) : Fintype.card V ≤ G.edgeSet.ncard + 1 := by
  have h := hConnected.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card (α := V)] at h
  have h2 : Nat.card G.edgeSet = G.edgeSet.ncard := (Nat.card_coe_set_eq _)
  omega
