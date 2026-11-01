-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_upper__p2m_ad02c9e2_6f74_49a1_ae0d_05fd18f8b6b9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:53:52.729686+00:00
-- url     : https://prove2.me/submissions/3df4d80f-0f90-433c-9276-9d43ee4896ca

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_from_drawing__p2m_c613d228_2a90_40f8_8150_998155f5275e_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_graph_edge_bound_from_drawing__p2m_c613d228_2a90_40f8_8150_998155f5275e_a1 H hH hcard