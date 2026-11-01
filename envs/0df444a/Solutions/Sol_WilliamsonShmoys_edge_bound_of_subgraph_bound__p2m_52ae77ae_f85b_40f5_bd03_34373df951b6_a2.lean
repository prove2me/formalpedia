-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_subgraph_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:51:51.392948+00:00
-- url     : https://prove2.me/submissions/c5009625-72c9-4f59-acfe-d2e97c1f821e

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V) [DecidableRel K.Adj] [DecidableRel H.Adj]
    (hKH : K ≤ H)
    (hHbound : H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) :
    K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  have hcard : K.edgeFinset.card ≤ H.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hKH)
  exact le_trans (Nat.add_le_add_right hcard 6) hHbound