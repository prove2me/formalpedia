-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_630b5c25_00a7_4258_a685_bfcae7eacbce_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:37:56.202687+00:00
-- url     : https://prove2.me/submissions/fa160b45-3ffc-4270-98f1-ee5b6abccfe8

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1 M hM hV hmax
