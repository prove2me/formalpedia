-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_630b5c25_00a7_4258_a685_bfcae7eacbce_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:59:09.733856+00:00
-- url     : https://prove2.me/submissions/08c39914-cb32-4b67-9cd5-f1502c3c1bf3

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound M hM hV
