-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:39:46.2313+00:00
-- url     : https://prove2.me/submissions/06ec2144-f4b3-42ec-8a65-64fb3d523adc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound_connected__p2m_14c57b1a_9d57_45d2_8a0d_6125974ddbe0_a1
import Theorems.Thm_WilliamsonShmoys_connect_planar_drawing_without_vertex_or_edge_loss__p2m_14c57b1a_9d57_45d2_8a0d_6125974ddbe0_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, _, hHdraw, hHconn, hLE⟩ :=
    WilliamsonShmoys.connect_planar_drawing_without_vertex_or_edge_loss__p2m_14c57b1a_9d57_45d2_8a0d_6125974ddbe0_a2
      L hL hcard
  have hH :=
    WilliamsonShmoys.planar_simple_graph_edge_upper_bound_connected__p2m_14c57b1a_9d57_45d2_8a0d_6125974ddbe0_a1
      H hHdraw hHconn hcard
  omega