-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_edgeSet_injective__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:34:12.261208+00:00
-- url     : https://prove2.me/submissions/14c5fd03-32bf-4ca4-b583-464391f60678

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] :
    Function.Injective (fun G : SimpleGraph V => G.edgeSet) := by
  exact SimpleGraph.edgeSet_injective