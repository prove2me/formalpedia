-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_graph_has_three_n_minus_six_edges__p2m_45533a44_b035_4e47_8a66_77352d0d9780_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:05:56.41991+00:00
-- url     : https://prove2.me/submissions/bfd7ee25-30d6-479c-82a7-c1804ed11cdf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_upper_bound__p2m_f302bffe_a312_4c80_ba34_5d3904b8242e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound__p2m_f302bffe_a312_4c80_ba34_5d3904b8242e_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys_maximal_planar_graph_edge_count_upper_bound__p2m_f302bffe_a312_4c80_ba34_5d3904b8242e_a1 L hcard hL
  have hlower := WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound__p2m_f302bffe_a312_4c80_ba34_5d3904b8242e_a1 L hcard hL hMax
  omega