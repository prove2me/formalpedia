-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound_4b22e7d2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T10:01:10.271731+00:00
-- url     : https://prove2.me/submissions/581c44c8-9972-4678-9644-46c9778783a5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_edge_maximal_graph

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.planar_edge_count_upper_bound_for_edge_maximal_graph
  | (apply _root_.WilliamsonShmoys.planar_edge_count_upper_bound_for_edge_maximal_graph <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_edge_count_upper_bound_for_edge_maximal_graph <;> assumption)
