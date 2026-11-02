-- Prove2me | solution 1 for WilliamsonShmoys.connected_card_le_edgeFinset_add_one__p2m_7f4c1ad2_4413_457d_ae8f_8936a6ba8a01_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:13:56.714959+00:00
-- url     : https://prove2.me/submissions/7d68d666-7cb1-4b98-985b-655938699d86

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected) :
    Fintype.card V ≤ H.edgeFinset.card + 1 := by
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
    hconn.card_vert_le_card_edgeSet_add_one