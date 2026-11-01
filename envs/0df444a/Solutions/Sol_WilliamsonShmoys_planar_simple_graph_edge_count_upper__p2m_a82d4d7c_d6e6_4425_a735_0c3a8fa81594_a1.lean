-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_count_upper__p2m_a82d4d7c_d6e6_4425_a735_0c3a8fa81594_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:18:50.60823+00:00
-- url     : https://prove2.me/submissions/da1e470d-439e-4581-bf4b-f999e73d8837

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawingOn_edge_bound K hK hcard
