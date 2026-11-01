-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_f88e8c23_22a3_4ff9_b09b_4991384a83f2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:12:38.760051+00:00
-- url     : https://prove2.me/submissions/9ed08023-198e-4431-827f-e51b95c4bd89

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a9
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a9 H hH hcard
