-- Prove2me | solution 1 for WilliamsonShmoys.strict_edge_card_of_strict_subgraph__p2m_6dfd0e85_ae5a_4e02_9c9b_5863f1785ef0_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:19:23.776514+00:00
-- url     : https://prove2.me/submissions/fc15251e-b930-4c72-a036-2c8dbab1983a

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    {G H : SimpleGraph V} [Fintype G.edgeSet] [Fintype H.edgeSet]
    (hGH : G ≤ H) (hne : G ≠ H) :
    G.edgeFinset.card < H.edgeFinset.card := by
  apply Finset.card_lt_card
  exact SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr
    (lt_of_le_of_ne hGH hne)