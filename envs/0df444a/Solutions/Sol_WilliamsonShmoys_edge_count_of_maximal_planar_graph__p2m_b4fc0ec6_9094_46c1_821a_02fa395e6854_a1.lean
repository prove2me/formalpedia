-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_b4fc0ec6_9094_46c1_821a_02fa395e6854_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:58:51.566339+00:00
-- url     : https://prove2.me/submissions/8adcade9-7bca-4010-ac4d-4f7f15697ee5

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_9518e4d8_9181_45e5_8d65_e8b1bfbc442a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_9518e4d8_9181_45e5_8d65_e8b1bfbc442a_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V, N <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hup := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_9518e4d8_9181_45e5_8d65_e8b1bfbc442a_a1
    N hcard hN
  have hlo := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_9518e4d8_9181_45e5_8d65_e8b1bfbc442a_a1
    N hcard hN hmax
  omega
