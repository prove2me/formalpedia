-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_70a8b6e0_c40a_44e8_9147_f9396a2e926b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:37:18.609629+00:00
-- url     : https://prove2.me/submissions/51d8e44f-5dce-49ed-997c-7fa02d462f56

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  have hlo := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1 M hM hCard hMax
  have hhi := WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1 M hM hCard
  omega