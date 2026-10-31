-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_1e4fc4c6_43c4_4ae0_af53_1d46a400a440_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:01:04.246931+00:00
-- url     : https://prove2.me/submissions/34f78572-9e8d-40e1-a8c2-75bfc468a229

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) (hCard : 3 ≤ Fintype.card V) : N.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_upper_bound N hN hCard
