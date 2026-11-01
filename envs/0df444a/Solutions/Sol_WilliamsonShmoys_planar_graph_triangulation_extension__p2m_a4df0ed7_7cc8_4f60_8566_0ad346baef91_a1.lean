-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_triangulation_extension__p2m_a4df0ed7_7cc8_4f60_8566_0ad346baef91_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:01:54.023473+00:00
-- url     : https://prove2.me/submissions/b7fc3d69-3f33-4483-b032-c2b621b3d22e

import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_a419e21a_2978_404e_8b1f_5dd1d0da8bd8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_a419e21a_2978_404e_8b1f_5dd1d0da8bd8_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_a419e21a_2978_404e_8b1f_5dd1d0da8bd8_a1 N hN
  refine ⟨K, hNK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_a419e21a_2978_404e_8b1f_5dd1d0da8bd8_a1 K hK hcard hmax