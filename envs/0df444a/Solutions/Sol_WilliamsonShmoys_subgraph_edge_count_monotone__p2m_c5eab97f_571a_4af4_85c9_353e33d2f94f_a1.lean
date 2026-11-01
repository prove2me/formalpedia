-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_edge_count_monotone__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:10:26.419887+00:00
-- url     : https://prove2.me/submissions/767328b3-95dc-4aec-ae1b-860e15282015

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K) :
    H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hHK)