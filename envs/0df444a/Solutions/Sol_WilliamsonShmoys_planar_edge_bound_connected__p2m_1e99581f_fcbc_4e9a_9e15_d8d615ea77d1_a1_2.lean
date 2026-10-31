-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_bound_connected__p2m_1e99581f_fcbc_4e9a_9e15_d8d615ea77d1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:40:00.463989+00:00
-- url     : https://prove2.me/submissions/cd3c6c8d-a7e5-4227-8132-bcca24fb3852

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_three_or_more_vertices_connected_core

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices_connected_core H hplanar hconn hV
