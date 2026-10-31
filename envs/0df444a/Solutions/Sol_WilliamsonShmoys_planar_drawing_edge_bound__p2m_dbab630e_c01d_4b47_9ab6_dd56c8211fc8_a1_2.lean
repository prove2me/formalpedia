-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_dbab630e_c01d_4b47_9ab6_dd56c8211fc8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:38:44.472309+00:00
-- url     : https://prove2.me/submissions/d96aea75-f6ef-4600-bc5a-fca3e04c8f3b

import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_from_embedding

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hConn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.connected_planar_drawing_edge_bound_from_embedding K hConn hK hCard
