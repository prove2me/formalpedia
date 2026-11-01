-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_extends_to_triangulation__p2m_7d8f15aa_1389_4e26_88fc_ab77a83aea4e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:54:16.88722+00:00
-- url     : https://prove2.me/submissions/74654f30-efe4-4b2f-a9a9-621f08c17882

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_b4fc0ec6_9094_46c1_821a_02fa395e6854_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph__p2m_b4fc0ec6_9094_46c1_821a_02fa395e6854_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_b4fc0ec6_9094_46c1_821a_02fa395e6854_a1
      M hcard hM
  refine ⟨N, hMN, hN, ?_⟩
  exact WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_b4fc0ec6_9094_46c1_821a_02fa395e6854_a1
    N hcard hN hmax