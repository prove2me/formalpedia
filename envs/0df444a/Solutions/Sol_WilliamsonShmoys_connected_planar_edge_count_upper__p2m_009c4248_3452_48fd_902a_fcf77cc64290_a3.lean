-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_upper__p2m_009c4248_3452_48fd_902a_fcf77cc64290_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:59:08.729109+00:00
-- url     : https://prove2.me/submissions/12170870-2773-487a-909e-75e1366fdb37

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_three_or_more_vertices_connected_core

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices_connected_core H hH hconn hV
