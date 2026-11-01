-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound_connected__p2m_14c57b1a_9d57_45d2_8a0d_6125974ddbe0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:21:53.10534+00:00
-- url     : https://prove2.me/submissions/6fdf6e8d-af42-404a-b97e-b2c072645459

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound L hL hcard
