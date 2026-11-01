-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_upper_bound__p2m_c0d4ecaf_266f_445a_8f51_dc327adf9453_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:13:28.34534+00:00
-- url     : https://prove2.me/submissions/2bbbecf9-1803-4aa5-9241-77401364c33f

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawingOn_edge_bound K hK hcard
