-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_202bf50d_736f_4a11_9464_01f4251d3269_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:14:27.944007+00:00
-- url     : https://prove2.me/submissions/3c1a6e9b-1122-4966-940d-e176433140b5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound__p2m_f88e8c23_22a3_4ff9_b09b_4991384a83f2_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_f88e8c23_22a3_4ff9_b09b_4991384a83f2_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J →
      J.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_f88e8c23_22a3_4ff9_b09b_4991384a83f2_a1
    H hcard hH
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_f88e8c23_22a3_4ff9_b09b_4991384a83f2_a1
    H hcard hH hmax
  omega