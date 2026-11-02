-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_subgraph_of_extremal_planar_graph__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:38:18.687595+00:00
-- url     : https://prove2.me/submissions/7530b1f2-f06b-4d66-b2a8-9042d6cfe66a

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V) (hMN : M ≤ N)
    (hN : (letI : DecidableRel N.Adj := Classical.decRel N.Adj
           N.edgeFinset.card + 6 = 3 * Fintype.card V)) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     letI : DecidableRel N.Adj := Classical.decRel N.Adj
     M.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  have hcard : M.edgeFinset.card ≤ N.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hMN)
  change N.edgeFinset.card + 6 = 3 * Fintype.card V at hN
  change M.edgeFinset.card + 6 ≤ 3 * Fintype.card V
  omega