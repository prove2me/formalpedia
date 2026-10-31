-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_edge_upper_bound__p2m_d61810ad_72dd_44a6_9339_c836b4de23da_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:14:23.590229+00:00
-- url     : https://prove2.me/submissions/b7c3abf7-6d86-451a-8dcc-e9eb030632ad

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_count_c7059b55_ff77_4f00_a57a_8983712db7a5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hLplanar : HasPlanarDrawingOn L) (hLconn : L.Connected) (hV : 3 ≤ Fintype.card V) : L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_connected_edge_count_c7059b55_ff77_4f00_a57a_8983712db7a5 L hLplanar hLconn hV
