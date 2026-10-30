-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_nat_edge_count_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:02:29.102055+00:00
-- url     : https://prove2.me/submissions/134f322d-6d51-4983-aaec-c42640d058ea

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_planar_completion_exact_edge_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count_for_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      N ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hNL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_planar_completion_exact_edge_count N hN
  refine ⟨L, hNL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_for_completion
    L hL hmax hCard