-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_edge_bound_for_job_f7651c89_84f0_476d_9038_b143112ca155
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:55:14.637612+00:00
-- url     : https://prove2.me/submissions/9d3c627d-5c58-4053-91b9-e551ff5efcd0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_drawable_supergraph_for_job_1741d11a_1189_4036_a189_421ad3678041
import Theorems.Thm_WilliamsonShmoys_edge_maximal_drawable_graph_edge_bound_for_job_1741d11a_1189_4036_a189_421ad3678041

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      Set.Subset L.edgeSet M.edgeSet ∧
      3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  obtain ⟨M, hM, hLM, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_drawable_supergraph_for_job_1741d11a_1189_4036_a189_421ad3678041 L hL
  refine ⟨M, hM, hLM, ?_⟩
  exact WilliamsonShmoys.edge_maximal_drawable_graph_edge_bound_for_job_1741d11a_1189_4036_a189_421ad3678041 M hM hmax hV