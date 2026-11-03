-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_261600ee_7fa4_4a45_a37b_002442c9d475_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:37:22.046196+00:00
-- url     : https://prove2.me/submissions/7dca81e3-8413-4948-809f-9c8cfe2cd914

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_e592f479_7758_40c0_97f7_ee5e29c0fee3_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_e592f479_7758_40c0_97f7_ee5e29c0fee3_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hLower := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_e592f479_7758_40c0_97f7_ee5e29c0fee3_a1 M hM hCard hMax
  have hUpper := WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_e592f479_7758_40c0_97f7_ee5e29c0fee3_a1 M hM hCard
  omega