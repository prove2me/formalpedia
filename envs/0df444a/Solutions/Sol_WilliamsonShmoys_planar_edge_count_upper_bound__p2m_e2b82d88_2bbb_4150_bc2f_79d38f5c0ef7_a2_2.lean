-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_e2b82d88_2bbb_4150_bc2f_79d38f5c0ef7_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:08:09.925004+00:00
-- url     : https://prove2.me/submissions/a3e55de4-0719-4081-b163-8f14e2af1280

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_upper_bound N hN hCard
