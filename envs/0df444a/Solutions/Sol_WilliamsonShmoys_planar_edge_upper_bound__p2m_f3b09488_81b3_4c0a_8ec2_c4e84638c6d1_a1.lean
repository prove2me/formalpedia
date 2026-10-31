-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:55:59.915248+00:00
-- url     : https://prove2.me/submissions/e4e67866-2fb8-42ed-b4ea-a71fea459520

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hPlanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 H hPlanar hV
