-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_fbd4abfa_95e6_415e_91e9_eb5757f71c9a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:54:25.719984+00:00
-- url     : https://prove2.me/submissions/b09cce7b-2384-43e2-9950-b0b6f3b96c00

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound K hDraw hV
