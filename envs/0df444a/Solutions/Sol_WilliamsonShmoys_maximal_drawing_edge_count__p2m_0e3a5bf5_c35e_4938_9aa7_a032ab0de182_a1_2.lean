-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawing_edge_count__p2m_0e3a5bf5_c35e_4938_9aa7_a032ab0de182_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:35:35.335986+00:00
-- url     : https://prove2.me/submissions/002c5d6f-8eaf-4aa3-9100-8f6b16b60c81

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_euler_7e0405ab

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_edge_count_euler_7e0405ab L hDraw hCard hMax
