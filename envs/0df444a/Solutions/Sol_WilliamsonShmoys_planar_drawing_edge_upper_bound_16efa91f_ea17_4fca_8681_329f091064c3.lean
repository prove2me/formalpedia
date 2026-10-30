-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound_16efa91f_ea17_4fca_8681_329f091064c3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:46:39.828717+00:00
-- url     : https://prove2.me/submissions/10dc8592-c165-40ec-b3bd-8d53c83dbf06

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_same_vertex_edge_bound_of_planar_drawing

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.same_vertex_edge_bound_of_planar_drawing
  | (apply _root_.WilliamsonShmoys.same_vertex_edge_bound_of_planar_drawing <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.same_vertex_edge_bound_of_planar_drawing <;> assumption)
