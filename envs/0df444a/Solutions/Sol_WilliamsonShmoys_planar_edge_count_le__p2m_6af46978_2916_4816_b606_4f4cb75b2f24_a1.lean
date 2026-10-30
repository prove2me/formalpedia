-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_le__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:39:33.392818+00:00
-- url     : https://prove2.me/submissions/9c6a75b7-f7cd-4fd0-8395-e8c1cfceda8e

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
