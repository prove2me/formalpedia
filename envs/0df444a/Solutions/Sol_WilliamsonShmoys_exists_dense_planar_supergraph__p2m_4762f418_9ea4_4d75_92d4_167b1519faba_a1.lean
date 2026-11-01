-- Prove2me | solution 1 for WilliamsonShmoys.exists_dense_planar_supergraph__p2m_4762f418_9ea4_4d75_92d4_167b1519faba_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:35:11.041213+00:00
-- url     : https://prove2.me/submissions/cd9a4a92-5e0a-4143-a2cc-6de66cd872f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_9339270d_9fc9_4b81_a23b_72e2e50fd8a3_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_bound__p2m_9339270d_9fc9_4b81_a23b_72e2e50fd8a3_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9339270d_9fc9_4b81_a23b_72e2e50fd8a3_a1
      H hH
  refine ⟨K, hHK, hKplanar, ?_⟩
  exact WilliamsonShmoys.maximal_planar_supergraph_edge_bound__p2m_9339270d_9fc9_4b81_a23b_72e2e50fd8a3_a1
    K hCard hKplanar hKmax