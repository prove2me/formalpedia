-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_ec6e17da_f4f8_4b4d_9b03_c6a0a660eda4_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:20:37.556673+00:00
-- url     : https://prove2.me/submissions/6d2bc9f7-eda5-445a-8f19-c7f2744a94a5

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, J ≤ K → HasPlanarDrawingOn K → K ≤ J) :
    J.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4 J hPlanar hV hMax
