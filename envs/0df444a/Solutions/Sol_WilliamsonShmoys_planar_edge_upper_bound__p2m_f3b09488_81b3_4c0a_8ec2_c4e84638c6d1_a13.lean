-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a13
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:55:25.651782+00:00
-- url     : https://prove2.me/submissions/0f4e9a36-df45-4de4-9021-17f27c93ceed

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 H hDrawing hV
