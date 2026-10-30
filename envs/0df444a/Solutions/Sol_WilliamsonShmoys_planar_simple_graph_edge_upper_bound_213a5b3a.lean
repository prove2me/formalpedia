-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound_213a5b3a
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:42:00.953677+00:00
-- url     : https://prove2.me/submissions/d15b6a09-cfcc-411e-8983-46be115d1c9c

import Mathlib
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
