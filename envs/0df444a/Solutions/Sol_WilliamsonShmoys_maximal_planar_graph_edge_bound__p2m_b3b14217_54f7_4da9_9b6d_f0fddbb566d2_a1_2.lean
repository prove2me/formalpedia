-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_b3b14217_54f7_4da9_9b6d_f0fddbb566d2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:12:14.185353+00:00
-- url     : https://prove2.me/submissions/b23bfae3-6c7a-488e-8f7d-80e5c30111b6

import Theorems.Thm_WilliamsonShmoys_drawing_upper_edge_bound
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.drawing_upper_edge_bound N hN hV
