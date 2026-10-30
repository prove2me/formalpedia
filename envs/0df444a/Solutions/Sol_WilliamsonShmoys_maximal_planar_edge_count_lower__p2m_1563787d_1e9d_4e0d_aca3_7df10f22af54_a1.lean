-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_1563787d_1e9d_4e0d_aca3_7df10f22af54_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:25:20.235104+00:00
-- url     : https://prove2.me/submissions/8e0a2139-5056-47ae-bdef-2d72552f9713
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq_from_drawing__p2m_cf5b9138_9b5a_4508_a5f4_a698107874c7_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  have heq := WilliamsonShmoys.maximal_planar_edge_count_eq_from_drawing__p2m_cf5b9138_9b5a_4508_a5f4_a698107874c7_a1
    H hH hV hmax
  omega