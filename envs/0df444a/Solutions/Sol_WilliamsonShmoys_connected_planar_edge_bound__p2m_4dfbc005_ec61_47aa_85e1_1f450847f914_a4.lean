-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_4dfbc005_ec61_47aa_85e1_1f450847f914_a4
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:19:32.872184+00:00
-- url     : https://prove2.me/submissions/ab6b1162-8f5c-44a0-a37b-2d7c30d98a00

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : M.Connected)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 M hM hcard
