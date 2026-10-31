-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_27b8a194_6c54_4ca3_a684_9503cbbde751_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:50:15.225511+00:00
-- url     : https://prove2.me/submissions/d81924d4-f26e-4014-a4a7-baa0f2b2d524

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    J.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound J hPlanar hV
