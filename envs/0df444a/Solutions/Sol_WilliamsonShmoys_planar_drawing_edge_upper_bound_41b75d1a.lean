-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound_41b75d1a
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:49:59.79816+00:00
-- url     : https://prove2.me/submissions/9f760f42-f3fa-46b1-891d-24b6c6740887

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1 M hM hV