-- Prove2me | solution 1 for WilliamsonShmoys.small_graph_edge_bound__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:57:25.067652+00:00
-- url     : https://prove2.me/submissions/4474d1e4-9ec6-4f65-ada5-943faf33fd34

import Theorems.Thm_WilliamsonShmoys_small_graph_edge_bound__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a2

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hn : Fintype.card V < 3) :
    letI : DecidableRel G.Adj := Classical.decRel _
    G.edgeFinset.card ≤ 3 * Fintype.card V - 3 :=
  WilliamsonShmoys.small_graph_edge_bound__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a2 G hn