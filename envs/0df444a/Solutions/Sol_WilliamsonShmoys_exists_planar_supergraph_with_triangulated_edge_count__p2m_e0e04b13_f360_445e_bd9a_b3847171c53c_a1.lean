-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_triangulated_edge_count__p2m_e0e04b13_f360_445e_bd9a_b3847171c53c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:43:21.075655+00:00
-- url     : https://prove2.me/submissions/c5b05045-ea1b-4e8c-8676-345e8173bf76
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_0d90a4e2_211c_41d9_a3e6_1089ea8087c9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_0d90a4e2_211c_41d9_a3e6_1089ea8087c9_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_0d90a4e2_211c_41d9_a3e6_1089ea8087c9_a1 G hG
  refine ⟨K, hGK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_0d90a4e2_211c_41d9_a3e6_1089ea8087c9_a1 K hV hK hmax