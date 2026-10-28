-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph_with_edge_bound__p2m_c73cf9ba_fcca_4a3b_853a_2c4df1119a23_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:35:40.475091+00:00
-- url     : https://prove2.me/submissions/07b8fb5f-6c23-48bf-a5a8-27f4ab0e48b5

import Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_max_edge_count__p2m_ff556b08_9bb8_4b65_af48_6c1ba6d375a5_a1
import Theorems.Thm_WilliamsonShmoys_simpleGraph_eq_of_edgeSet_ncard_le__p2m_ff556b08_9bb8_4b65_af48_6c1ba6d375a5_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) ∧
      G.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_drawable_supergraph_max_edge_count__p2m_ff556b08_9bb8_4b65_af48_6c1ba6d375a5_a1 G hG
  refine ⟨K, hGK, hK, ?_, ?_⟩
  · intro L hKL hL
    exact WilliamsonShmoys.simpleGraph_eq_of_edgeSet_ncard_le__p2m_ff556b08_9bb8_4b65_af48_6c1ba6d375a5_a1
      K L hKL (hmax L hKL hL)
  · exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGK)