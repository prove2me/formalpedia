-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_4a772063d306_45bd_a029_619aef07cba4_a11
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:40:59.447397+00:00
-- url     : https://prove2.me/submissions/faae9911-e5a0-4cde-998e-037f3ae48932

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_face_accounting_57972424

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hConnected : T.Connected)
    (hV : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound_for_face_accounting_57972424 T hT hConnected hV
