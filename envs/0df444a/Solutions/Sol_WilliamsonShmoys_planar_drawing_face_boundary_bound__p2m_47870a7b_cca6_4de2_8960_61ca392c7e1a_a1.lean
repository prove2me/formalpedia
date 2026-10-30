-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_boundary_bound__p2m_47870a7b_cca6_4de2_8960_61ca392c7e1a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:03:12.575016+00:00
-- url     : https://prove2.me/submissions/ec5067b4-3eef-46b7-b8c8-a8ee0f0077c0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_04f4db05_702a_494d_b920_fe439899ceaa_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) (F : ℕ)
    (hEuler : Fintype.card V + F = K.edgeSet.ncard + 2) :
    3 * F ≤ 2 * K.edgeSet.ncard := by
  have hedge := WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_04f4db05_702a_494d_b920_fe439899ceaa_a1
    K hconn hdraw hV
  omega