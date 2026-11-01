-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_b4696467_bd7a_4833_91a4_199ab5144504_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:18:26.044274+00:00
-- url     : https://prove2.me/submissions/be773b1e-0211-41e9-b335-3c36d87f1ce9

import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_for_certificate

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_simple_edge_bound_for_certificate K hcard hplanar
