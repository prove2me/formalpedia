-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c298a3e1_504a_4c1d_8a31_03ab929cfe86_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:10:31.329978+00:00
-- url     : https://prove2.me/submissions/ee974910-294b-4fa9-b4d1-d68b38de44da

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V) :
    P.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 P hDraw hCard
