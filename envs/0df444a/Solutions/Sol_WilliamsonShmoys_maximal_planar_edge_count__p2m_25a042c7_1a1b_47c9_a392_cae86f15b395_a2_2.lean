-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_25a042c7_1a1b_47c9_a392_cae86f15b395_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:14:18.279489+00:00
-- url     : https://prove2.me/submissions/f50a489c-5683-42f7-ab8d-d9154a2705b8

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6a8f39b0_bd46_412b_a379_1f5e129b67f1_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count__p2m_6a8f39b0_bd46_412b_a379_1f5e129b67f1_a1 K hK hcard hmax
