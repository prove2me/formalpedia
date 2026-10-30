-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:11:07.536413+00:00
-- url     : https://prove2.me/submissions/5f3121c4-09f2-4047-ba78-8ef40354e328

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_2026

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_simple_graph_edge_bound_2026
  | (apply _root_.WilliamsonShmoys.planar_simple_graph_edge_bound_2026 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_simple_graph_edge_bound_2026 <;> assumption)
