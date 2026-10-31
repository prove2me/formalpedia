-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound__p2m_c50fd7db_db60_4155_a74b_9f8219c920fe_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:20:30.506991+00:00
-- url     : https://prove2.me/submissions/8a72e09d-1bd9-479e-ab26-f689feb8c6b7

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound H hPlanar hV
