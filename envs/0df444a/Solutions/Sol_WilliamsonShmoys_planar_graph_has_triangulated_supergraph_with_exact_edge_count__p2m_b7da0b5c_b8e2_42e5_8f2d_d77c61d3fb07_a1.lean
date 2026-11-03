-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_supergraph_with_exact_edge_count__p2m_b7da0b5c_b8e2_42e5_8f2d_d77c61d3fb07_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:45:16.981916+00:00
-- url     : https://prove2.me/submissions/88d52c8d-0ccc-43e2-9dac-4f110126bdeb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_86ac92fe_a077_498c_8a86_bf0c24de864c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_exact_edge_count__p2m_86ac92fe_a077_498c_8a86_bf0c24de864c_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ Q : SimpleGraph V,
      G ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        (letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
         3 * Fintype.card V = Q.edgeFinset.card + 6) := by
  obtain ⟨Q, hGQ, hQ, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_86ac92fe_a077_498c_8a86_bf0c24de864c_a1
      G hG
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count__p2m_86ac92fe_a077_498c_8a86_bf0c24de864c_a1
      Q hQ hcard hmax
  exact ⟨Q, hGQ, hQ, hcount⟩