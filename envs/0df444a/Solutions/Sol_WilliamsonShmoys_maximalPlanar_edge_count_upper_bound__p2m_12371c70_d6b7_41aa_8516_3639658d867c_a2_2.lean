-- Prove2me | solution 2 for WilliamsonShmoys.maximalPlanar_edge_count_upper_bound__p2m_12371c70_d6b7_41aa_8516_3639658d867c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:34:10.184204+00:00
-- url     : https://prove2.me/submissions/e769df02-8b30-487e-afac-8b61df36bfc7

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 N hN hCard
