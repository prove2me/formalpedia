-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_edge_ncard_mono__p2m_9786a817_f7aa_4876_b28c_017cd5fca12a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:06:42.347135+00:00
-- url     : https://prove2.me/submissions/5e0b82bd-410f-4686-820e-4c81e586a215

import Mathlib

theorem solution {V : Type} [Fintype V] (G K : SimpleGraph V) (h : G ≤ K) :
    G.edgeSet.ncard ≤ K.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono h)