-- Prove2me | solution 2 for WilliamsonShmoys.planar_maximal_extension_count__p2m_ac6eb2e4_2427_46c2_b7cd_156017af8bc0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:28:16.509999+00:00
-- url     : https://prove2.me/submissions/44ccf070-87c4-4605-9222-5417c62238ef

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_has_triangulated_extension

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : ∃ J : SimpleGraph V, G ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧ J.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawingOn_has_triangulated_extension G hDraw hCard
