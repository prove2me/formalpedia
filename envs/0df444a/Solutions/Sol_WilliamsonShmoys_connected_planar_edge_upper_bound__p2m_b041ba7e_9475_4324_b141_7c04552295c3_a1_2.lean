-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_b041ba7e_9475_4324_b141_7c04552295c3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:53:04.386243+00:00
-- url     : https://prove2.me/submissions/42767670-b9b1-44ef-a20b-85299566a1dc

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_three_or_more_vertices_connected_core

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices_connected_core H hH hconn hV
