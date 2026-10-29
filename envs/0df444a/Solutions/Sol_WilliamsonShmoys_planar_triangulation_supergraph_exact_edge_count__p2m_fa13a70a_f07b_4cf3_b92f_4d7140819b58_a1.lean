-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_fa13a70a_f07b_4cf3_b92f_4d7140819b58_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:55:31.100483+00:00
-- url     : https://prove2.me/submissions/4ae29bbd-3320-43b1-8900-e251c351d0df

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_f624320d_e63d_47e0_83d6_ecbceca14194_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count__p2m_f624320d_e63d_47e0_83d6_ecbceca14194_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 ∧
      WilliamsonShmoys.HasPlanarDrawingOn N := by
  obtain ⟨N, hEdge, _hMN, hMaximal, hN⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_f624320d_e63d_47e0_83d6_ecbceca14194_a1
      M hV hM
  refine ⟨N, hEdge, ?_, hN⟩
  exact WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_f624320d_e63d_47e0_83d6_ecbceca14194_a1
    N hV hMaximal hN