-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:27:48.3794+00:00
-- url     : https://prove2.me/submissions/3aa40aa6-a363-435f-ada3-6a4848778856

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 M hDraw hCard
