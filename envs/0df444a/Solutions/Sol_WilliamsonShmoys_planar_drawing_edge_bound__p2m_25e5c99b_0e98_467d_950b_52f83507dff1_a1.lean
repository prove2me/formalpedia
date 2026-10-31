-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:59:09.356539+00:00
-- url     : https://prove2.me/submissions/0effa074-02a1-4aa5-8892-1942dadd92b1

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_upper_bound G hG hV
