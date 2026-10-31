-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_edge_count_monotone__p2m_1fea64f0_2aef_4373_b504_03974af27e28_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:25:46.073545+00:00
-- url     : https://prove2.me/submissions/f6417149-19f1-407e-a18e-df4ce17d955a

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (G H : SimpleGraph V) (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH)