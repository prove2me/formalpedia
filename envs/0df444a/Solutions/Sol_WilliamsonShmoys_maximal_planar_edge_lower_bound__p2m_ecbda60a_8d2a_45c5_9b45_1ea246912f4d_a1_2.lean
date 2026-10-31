-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ecbda60a_8d2a_45c5_9b45_1ea246912f4d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:39:30.355616+00:00
-- url     : https://prove2.me/submissions/63f103fb-55c4-4e50-bd36-b6a1fb0de508

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1 L hL hCard hMax
