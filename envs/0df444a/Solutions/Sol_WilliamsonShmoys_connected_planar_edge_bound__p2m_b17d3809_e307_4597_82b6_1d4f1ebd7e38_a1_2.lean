-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_edge_bound__p2m_b17d3809_e307_4597_82b6_1d4f1ebd7e38_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:14:24.709865+00:00
-- url     : https://prove2.me/submissions/8e1c1b57-e5b9-411e-a92f-6cc7dfb790f2

import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hConn : P.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    P.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.connected_planar_edge_count_bound__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4 P hDraw hConn hCard
