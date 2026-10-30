-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:11:20.994796+00:00
-- url     : https://prove2.me/submissions/8259cd95-a514-416b-ad3b-c41d0ae2aa9f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V) (hHK : H ≤ K) :
    H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hHK)