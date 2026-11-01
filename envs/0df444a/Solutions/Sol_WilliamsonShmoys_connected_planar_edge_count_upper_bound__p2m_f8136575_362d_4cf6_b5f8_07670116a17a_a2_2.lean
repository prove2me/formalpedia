-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_f8136575_362d_4cf6_b5f8_07670116a17a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:20:38.092085+00:00
-- url     : https://prove2.me/submissions/43f0f637-fab8-4512-869a-061498a239c5

import Theorems.Thm_WilliamsonShmoys_edge_count_planar_upper_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.edge_count_planar_upper_retry3 G hplanar hcard
