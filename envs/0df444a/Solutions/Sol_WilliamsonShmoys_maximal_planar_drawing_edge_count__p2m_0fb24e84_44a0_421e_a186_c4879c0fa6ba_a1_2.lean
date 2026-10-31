-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_0fb24e84_44a0_421e_a186_c4879c0fa6ba_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:33:53.991142+00:00
-- url     : https://prove2.me/submissions/1167e3b9-df0f-40fa-85a8-b87c65d1fe30

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_19f31498_c1c5_41a0_a186_562a063d6dde

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = L.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count_19f31498_c1c5_41a0_a186_562a063d6dde L hV hDraw hmax
