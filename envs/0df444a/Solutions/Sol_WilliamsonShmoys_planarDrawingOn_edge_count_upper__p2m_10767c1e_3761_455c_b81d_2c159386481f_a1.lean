-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_edge_count_upper__p2m_10767c1e_3761_455c_b81d_2c159386481f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:42:14.505196+00:00
-- url     : https://prove2.me/submissions/f52b7026-95b2-43dd-ab67-eced75e743b2

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawingOn_edge_bound K hK hCard