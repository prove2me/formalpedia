-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_105a7e64_a154_40f8_8dae_11517fa32419_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:15:39.212978+00:00
-- url     : https://prove2.me/submissions/12d310e6-31bd-4805-aa27-e2d98cae6102

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_has_triangulated_extension

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

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
