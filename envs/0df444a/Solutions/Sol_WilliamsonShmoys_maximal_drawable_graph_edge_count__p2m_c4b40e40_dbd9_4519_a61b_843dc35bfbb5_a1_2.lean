-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:16:22.397215+00:00
-- url     : https://prove2.me/submissions/9bcda11e-2b54-440f-befa-cc24fa75f82b

import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_94348bb4_0897_41cb_a4e2_91f9fb7adb36
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 = M.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_graph_edge_count_94348bb4_0897_41cb_a4e2_91f9fb7adb36 M hM hcard hmax
