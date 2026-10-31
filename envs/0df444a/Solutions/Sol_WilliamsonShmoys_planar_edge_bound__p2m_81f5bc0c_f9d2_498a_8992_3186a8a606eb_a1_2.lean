-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_bound__p2m_81f5bc0c_f9d2_498a_8992_3186a8a606eb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T20:48:00.571935+00:00
-- url     : https://prove2.me/submissions/e2744503-4980-4084-a1f9-4f3023b28975

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_repair3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_edge_upper_bound_repair3 N hCard hN
