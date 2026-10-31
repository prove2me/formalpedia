-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_c8bd0d06_bddd_4d97_9a5a_50d50f58bad7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:34:55.148085+00:00
-- url     : https://prove2.me/submissions/2f2e09c3-9891-49eb-99d3-e65299bd1be0

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_has_triangulated_extension

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawingOn_has_triangulated_extension L hplanar hV
