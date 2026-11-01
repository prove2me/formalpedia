-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_edge_bound_from_drawing__p2m_c613d228_2a90_40f8_8150_998155f5275e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:22:49.974566+00:00
-- url     : https://prove2.me/submissions/c6fa7b9f-087a-42ef-b1ff-ece36818b80f

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2 H hcard hH
