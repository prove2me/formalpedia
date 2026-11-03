-- Prove2me | solution 1 for WilliamsonShmoys.planar_edgeSet_ncard_le_three_mul_card_sub_six__p2m_b8afd70d_5e18_4708_a739_37d2bdc4e576_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:39:59.432462+00:00
-- url     : https://prove2.me/submissions/0637bcd2-b745-4a77-96c0-db3016196314

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_upper_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound K hcard hplanar