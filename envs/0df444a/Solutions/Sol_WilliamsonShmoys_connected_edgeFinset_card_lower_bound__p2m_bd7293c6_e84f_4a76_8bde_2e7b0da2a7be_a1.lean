-- Prove2me | solution 1 for WilliamsonShmoys.connected_edgeFinset_card_lower_bound__p2m_bd7293c6_e84f_4a76_8bde_2e7b0da2a7be_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:13:50.530178+00:00
-- url     : https://prove2.me/submissions/c54c9ddc-a4cc-4d30-b6d7-39da982a5c12

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hconn : L.Connected) :
    Fintype.card V - 1 ≤ (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) := by
  letI : DecidableRel L.Adj := dL
  have h := hconn.card_vert_le_card_edgeSet_add_one
  have h' : Fintype.card V ≤ L.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, ← L.edgeFinset_card] using h
  omega