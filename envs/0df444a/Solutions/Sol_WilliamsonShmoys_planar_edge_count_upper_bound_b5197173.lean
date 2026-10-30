-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_b5197173
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:56:44.753487+00:00
-- url     : https://prove2.me/submissions/49e15296-30bd-40ec-a884-76a4c4009b38

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_graph_edge_bound_from_arcs

set_option autoImplicit false


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.planar_drawable_graph_edge_bound_from_arcs
  | (apply _root_.WilliamsonShmoys.planar_drawable_graph_edge_bound_from_arcs <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_drawable_graph_edge_bound_from_arcs <;> assumption)
