-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_44b3e4a1_3366_4047_b54d_bdbe1bcd0716_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:32:51.536338+00:00
-- url     : https://prove2.me/submissions/d3343b4b-6ab6-41ba-8e35-d8a46d2d5a73

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_v2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_v2 H hH hmax hV
