-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_ec7a7294_2e22_40b0_b436_8d0de67c32fd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:30:54.704023+00:00
-- url     : https://prove2.me/submissions/fa0c425a-0b28-4cd0-b38a-a3a3d86696e3

import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_for_triangulation_exact_edge_count

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard :=
  WilliamsonShmoys.edge_count_of_maximal_planar_drawing_for_triangulation_exact_edge_count L hV hL hmax
