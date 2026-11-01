-- Prove2me | solution 1 for WilliamsonShmoys.connected_edge_card_lower_bound__p2m_a78a6ebd_f14e_4d5e_887a_7bf11c56fcc6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:21:23.289392+00:00
-- url     : https://prove2.me/submissions/7d291859-0963-4e99-92c3-d94d03057030

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected) :
    Fintype.card V ≤ H.edgeFinset.card + 1 := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] using h