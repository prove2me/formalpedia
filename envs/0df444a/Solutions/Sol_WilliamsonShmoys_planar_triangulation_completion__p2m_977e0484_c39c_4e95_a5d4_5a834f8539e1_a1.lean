-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_977e0484_c39c_4e95_a5d4_5a834f8539e1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:47:18.102247+00:00
-- url     : https://prove2.me/submissions/80f6a32b-9d3a-4c3c-a0f5-c535b669eb2a

import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal__p2m_b6e1b838_6a07_4127_97a1_2301fa6a9ddd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_b6e1b838_6a07_4127_97a1_2301fa6a9ddd_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨N, hMN, hN, hmax⟩ := WilliamsonShmoys.exists_planar_supergraph_maximal__p2m_b6e1b838_6a07_4127_97a1_2301fa6a9ddd_a1 M hcard hM
  refine ⟨N, hMN, hN, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b6e1b838_6a07_4127_97a1_2301fa6a9ddd_a1 N hcard hN hmax