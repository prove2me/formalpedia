-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:12:10.90285+00:00
-- url     : https://prove2.me/submissions/73eb3c99-d9f3-489c-a27e-dea00aafdd5d

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound M hM hCard
