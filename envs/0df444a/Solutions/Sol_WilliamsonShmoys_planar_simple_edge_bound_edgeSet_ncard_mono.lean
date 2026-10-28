-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound_edgeSet_ncard_mono
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:04:10.657559+00:00
-- url     : https://prove2.me/submissions/b31b17e1-9692-49df-a0fe-45aaa780602a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hGH)