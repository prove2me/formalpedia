-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_eq_from_drawing__p2m_cf5b9138_9b5a_4508_a5f4_a698107874c7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:29:12.024925+00:00
-- url     : https://prove2.me/submissions/b3e7d76d-6935-4d98-9390-027371685aab

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1 H hH hV
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1 H hH hV hmax
  omega