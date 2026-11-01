-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_0d2111fe_49a0_4983_b8b9_46fbb1acc127_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:11:16.216211+00:00
-- url     : https://prove2.me/submissions/d898a1d5-04a3-4134-b9e3-a08dc24f0751

import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_bf226c5d
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_simple_edge_bound_bf226c5d G hCard hG
