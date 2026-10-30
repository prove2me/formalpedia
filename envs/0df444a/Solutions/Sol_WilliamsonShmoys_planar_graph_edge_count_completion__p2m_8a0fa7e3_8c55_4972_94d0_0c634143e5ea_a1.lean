-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_count_completion__p2m_8a0fa7e3_8c55_4972_94d0_0c634143e5ea_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T11:58:43.199239+00:00
-- url     : https://prove2.me/submissions/1d9c8b35-76ab-44d5-aa4a-a93dfba11272

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximality__p2m_dc74ed81_22cf_4790_bfe4_28c52731184f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_dc74ed81_22cf_4790_bfe4_28c52731184f_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet ⊆ K.edgeSet ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hK, hHK, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximality__p2m_dc74ed81_22cf_4790_bfe4_28c52731184f_a1 H hH
  refine ⟨K, hK, hHK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_dc74ed81_22cf_4790_bfe4_28c52731184f_a1 K hK hV hmax