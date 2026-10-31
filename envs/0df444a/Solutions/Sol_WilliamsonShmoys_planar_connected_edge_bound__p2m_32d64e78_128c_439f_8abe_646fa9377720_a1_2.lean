-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_edge_bound__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:40:53.863986+00:00
-- url     : https://prove2.me/submissions/e89c7de5-9081-4523-a3a5-644ee80c9365

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_face_accounting_57972424

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound_for_face_accounting_57972424 H hH hconn hV
