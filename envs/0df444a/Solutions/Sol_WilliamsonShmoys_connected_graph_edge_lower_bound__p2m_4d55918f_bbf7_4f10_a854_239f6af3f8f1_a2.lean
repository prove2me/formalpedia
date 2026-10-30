-- Prove2me | solution 1 for WilliamsonShmoys.connected_graph_edge_lower_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:30:59.760011+00:00
-- url     : https://prove2.me/submissions/9fa1522f-bbaa-4353-9802-cb6843c684d0

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Set.Card

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected) :
    Fintype.card V <= K.edgeSet.ncard + 1 := by
  simpa only [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
    hconn.card_vert_le_card_edgeSet_add_one