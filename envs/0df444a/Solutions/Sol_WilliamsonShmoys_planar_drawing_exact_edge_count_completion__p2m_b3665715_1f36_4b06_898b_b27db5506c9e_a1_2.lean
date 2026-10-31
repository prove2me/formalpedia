-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_b3665715_1f36_4b06_898b_b27db5506c9e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:15:54.868005+00:00
-- url     : https://prove2.me/submissions/0ff0b716-f87d-40c7-b842-046e5e49172d

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_has_triangulated_extension

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawingOn_has_triangulated_extension G hG hV
