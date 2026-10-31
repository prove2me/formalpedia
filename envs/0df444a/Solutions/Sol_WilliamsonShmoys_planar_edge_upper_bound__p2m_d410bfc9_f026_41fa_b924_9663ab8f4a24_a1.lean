-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_d410bfc9_f026_41fa_b924_9663ab8f4a24_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:58:02.771885+00:00
-- url     : https://prove2.me/submissions/03e8359c-ec57-48bb-8073-6da80efb4137

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_repair3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_edge_upper_bound_repair3 M hV hM
