-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_c603be23_9a74_4dd9_9858_66dd86a4b903_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:28:47.134498+00:00
-- url     : https://prove2.me/submissions/7a10d0b7-c84f-4ffc-aee3-32897ee5e2d6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ecbda60a_8d2a_45c5_9b45_1ea246912f4d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ecbda60a_8d2a_45c5_9b45_1ea246912f4d_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.planar_edge_upper_bound__p2m_ecbda60a_8d2a_45c5_9b45_1ea246912f4d_a1 L hL hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ecbda60a_8d2a_45c5_9b45_1ea246912f4d_a1 L hL hCard hMax
  omega