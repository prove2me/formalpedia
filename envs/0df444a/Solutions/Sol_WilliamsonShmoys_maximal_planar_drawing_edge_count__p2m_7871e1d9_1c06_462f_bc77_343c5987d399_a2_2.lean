-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_7871e1d9_1c06_462f_bc77_343c5987d399_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:35:12.438579+00:00
-- url     : https://prove2.me/submissions/ad4cd870-6501-44c7-bec2-d9e6d1842a70

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_1a5a4a98_d076_4be8_9c0b_d5fb8ab1d149_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ H : SimpleGraph V, M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_drawable_edge_count__p2m_1a5a4a98_d076_4be8_9c0b_d5fb8ab1d149_a1 M hDraw hV hMax
