-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_edge_count_upper__p2m_9f29656c_dc34_4a7a_a3c2_ff1f2fc6d96d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:40:00.761524+00:00
-- url     : https://prove2.me/submissions/9b4e9573-3b72-4471-95e6-885eb878e1b8

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_three_or_more_vertices_connected_core

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hConn : M.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices_connected_core M hM hConn hCard
