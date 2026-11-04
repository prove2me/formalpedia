-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_8c9864f5_741a_481d_8578_325697296ee9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:10:45.059996+00:00
-- url     : https://prove2.me/submissions/a9b8930d-f39f-4e7f-b5fa-1410f82dad44

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_34c1d13a_c463_44f3_a4ff_eb6476f05c93_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_34c1d13a_c463_44f3_a4ff_eb6476f05c93_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ T : SimpleGraph V, G ≤ T ∧ HasPlanarDrawingOn T ∧
      (letI : DecidableRel T.Adj := Classical.decRel T.Adj
       T.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨T, hGT, hT, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_34c1d13a_c463_44f3_a4ff_eb6476f05c93_a2 G hV hG
  refine ⟨T, hGT, hT, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_34c1d13a_c463_44f3_a4ff_eb6476f05c93_a2 T hV hT hmax