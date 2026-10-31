-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_from_drawing__p2m_9b9fadfe_20c3_484e_b25c_37db0802734a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:06:55.110779+00:00
-- url     : https://prove2.me/submissions/22a2b3df-ad99-4a03-97dd-1f3e860e4cf9

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S) (hCard : 3 ≤ Fintype.card V) : S.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 S hS hCard
