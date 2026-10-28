-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulated_completion_edge_count_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:12:34.01593+00:00
-- url     : https://prove2.me/submissions/a594a9f3-1d00-42f9-b2f2-9e92c6d10b66

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G K : SimpleGraph V)
    (hSub : G ≤ K) :
    G.edgeSet.ncard ≤ K.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr hSub)