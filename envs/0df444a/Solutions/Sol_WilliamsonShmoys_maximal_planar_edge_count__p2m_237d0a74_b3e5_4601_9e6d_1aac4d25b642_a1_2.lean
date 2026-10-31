-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_237d0a74_b3e5_4601_9e6d_1aac4d25b642_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:16:41.653132+00:00
-- url     : https://prove2.me/submissions/16155a94-7474-41ef-8333-dedb741dd176

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_7ccdbe8d_8a58_4fea_8872_faa4254f94f9_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard ≤ L.edgeSet.ncard) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_7ccdbe8d_8a58_4fea_8872_faa4254f94f9_a1 L hplanar hV hmax
