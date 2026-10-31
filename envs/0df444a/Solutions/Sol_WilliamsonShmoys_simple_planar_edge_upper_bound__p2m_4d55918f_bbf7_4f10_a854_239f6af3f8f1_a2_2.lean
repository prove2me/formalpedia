-- Prove2me | solution 2 for WilliamsonShmoys.simple_planar_edge_upper_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:32:49.753991+00:00
-- url     : https://prove2.me/submissions/ee867eb7-6202-4aba-a0d9-e63a1cbd1048

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 K hK hV
