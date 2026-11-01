-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_abcc1e5a_cabd_49d6_8da8_bf017a643b84_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:12:22.510706+00:00
-- url     : https://prove2.me/submissions/b1e09fe6-99f5-4632-9380-aad8ef82402c

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_job_09cd0f78_596e_4a94_9326_038b3be8d638

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_count_upper_bound_job_09cd0f78_596e_4a94_9326_038b3be8d638 L hL hcard
