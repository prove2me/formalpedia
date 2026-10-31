-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_7cbc47d5_f864_41b7_a55a_235c34cff0ec_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:33:23.900957+00:00
-- url     : https://prove2.me/submissions/f4d586ce-f3ca-4ce1-8234-4e3ff698c4a4

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4 H hH hV hmax
