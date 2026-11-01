-- Prove2me | solution 1 for WilliamsonShmoys.edge_ncard_mono__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:58:56.475188+00:00
-- url     : https://prove2.me/submissions/d2b192e2-ce92-4731-b15e-dfe7a6570555

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH)