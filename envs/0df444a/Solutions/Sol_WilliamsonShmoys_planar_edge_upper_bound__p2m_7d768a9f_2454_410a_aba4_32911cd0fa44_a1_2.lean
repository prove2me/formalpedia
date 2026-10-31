-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_upper_bound__p2m_7d768a9f_2454_410a_aba4_32911cd0fa44_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:06:55.107101+00:00
-- url     : https://prove2.me/submissions/e69f94eb-48b3-4f33-b9e2-adfc18da0e17

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 H hH hV
