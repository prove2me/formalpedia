-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_bound__p2m_fa1358d7_5b01_463f_a67b_1e1bbf77dca7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:42:57.853579+00:00
-- url     : https://prove2.me/submissions/b95b5449-974d-4477-b400-a9ef5274a983

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 H hH hCard
