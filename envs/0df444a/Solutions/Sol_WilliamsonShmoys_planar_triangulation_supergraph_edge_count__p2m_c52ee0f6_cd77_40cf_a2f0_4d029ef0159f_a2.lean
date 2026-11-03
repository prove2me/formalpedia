-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_c52ee0f6_cd77_40cf_a2f0_4d029ef0159f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:50:17.725129+00:00
-- url     : https://prove2.me/submissions/51a5cfcc-0885-405b-a484-93d546af0517

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists__p2m_cc6eda38_1b75_4537_8542_c84b46a8d9a9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_cc6eda38_1b75_4537_8542_c84b46a8d9a9_a1

set_option autoImplicit false

open scoped BigOperators

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun H : SimpleGraph V =>
      K <= H /\
      WilliamsonShmoys.HasPlanarDrawingOn H /\
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_cc6eda38_1b75_4537_8542_c84b46a8d9a9_a1 K hK
  refine ⟨H, hKH, hH, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_cc6eda38_1b75_4537_8542_c84b46a8d9a9_a1 H hcard hH hmax