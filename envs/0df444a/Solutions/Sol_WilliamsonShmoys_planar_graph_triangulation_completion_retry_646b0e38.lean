-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_triangulation_completion_retry_646b0e38
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:41:01.197895+00:00
-- url     : https://prove2.me/submissions/6281b624-56d9-4df8-8821-7202b6117f2c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximal_retry_646b0e38
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_retry_646b0e38

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.finite_planar_supergraph_maximal_retry_646b0e38 M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_retry_646b0e38 N hV hN hmax⟩