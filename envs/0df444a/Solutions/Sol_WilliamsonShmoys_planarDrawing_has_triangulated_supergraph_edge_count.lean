-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_has_triangulated_supergraph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:48:33.104292+00:00
-- url     : https://prove2.me/submissions/79b9f364-6403-48d3-8148-0dcc42272424

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_exists_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximalPlanar_has_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planarDrawing_exists_maximal_supergraph M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximalPlanar_has_edge_count N hN hCard hmax⟩