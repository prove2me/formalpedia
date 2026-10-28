-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_count_upper_bound_dabb2cbe_7fe3_4213_96ba_204afbbd922b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:00:52.112015+00:00
-- url     : https://prove2.me/submissions/300f4f3b-3c25-41e7-80af-7fca38163901
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_graph_edge_count
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    Y.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨Z, hYZ, hmono, hconn, hdraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_v2 Y hY
  have hbound :=
    WilliamsonShmoys.connected_planar_graph_edge_count Z hV hconn hdraw
  omega