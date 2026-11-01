-- Prove2me | solution 1 for WilliamsonShmoys.card_le_edgeFinset_add_one_of_connected__p2m_de496d36_7d00_43e9_8f8b_fa9ee9576ec1_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:55:20.544388+00:00
-- url     : https://prove2.me/submissions/94fd0566-aa8a-484a-beb1-1062459d1850

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hconn : K.Connected) :
    Fintype.card V ≤ K.edgeFinset.card + 1 := by
  simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] using
    SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one hconn