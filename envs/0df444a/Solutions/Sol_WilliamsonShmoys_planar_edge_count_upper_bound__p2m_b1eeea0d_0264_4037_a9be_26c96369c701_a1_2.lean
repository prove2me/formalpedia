-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:18:09.041288+00:00
-- url     : https://prove2.me/submissions/5421d291-2e82-4e9c-b4f9-3e637796bca7

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawingOn_edge_bound K hK hcard
