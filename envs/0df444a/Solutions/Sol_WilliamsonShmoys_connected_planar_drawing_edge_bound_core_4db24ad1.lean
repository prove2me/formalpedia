-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound_core_4db24ad1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:54:01.840107+00:00
-- url     : https://prove2.me/submissions/cc33e1f7-703c-4039-bd52-6a05375a3a75

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_simple_planar_graph_edge_bound_of_drawing

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.connected_simple_planar_graph_edge_bound_of_drawing
  | (apply _root_.WilliamsonShmoys.connected_simple_planar_graph_edge_bound_of_drawing <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.connected_simple_planar_graph_edge_bound_of_drawing <;> assumption)
