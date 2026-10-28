-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound_from_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:46:44.470909+00:00
-- url     : https://prove2.me/submissions/a2f9b852-fb09-4468-a096-48299199b3b8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_edge_bound
import Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_edge_bound_euler

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hsub, hcard, hconn, hdraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation_edge_bound G hG hV
  have hbound :=
    WilliamsonShmoys.connected_planar_simple_graph_edge_bound_euler H hdraw hconn hV
  exact hcard.trans hbound