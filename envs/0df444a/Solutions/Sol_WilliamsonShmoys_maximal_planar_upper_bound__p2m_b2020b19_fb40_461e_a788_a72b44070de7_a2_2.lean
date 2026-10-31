-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_upper_bound__p2m_b2020b19_fb40_461e_a788_a72b44070de7_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:59:22.961001+00:00
-- url     : https://prove2.me/submissions/d19225e4-5d69-468f-adde-1c1f55b9393b

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 K hK hV
