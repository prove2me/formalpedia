-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_c603be23_9a74_4dd9_9858_66dd86a4b903_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:32:17.700869+00:00
-- url     : https://prove2.me/submissions/3489c5cf-37a7-4f01-b404-ad615869d916

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_count_bound_v2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_for_edge_count_bound_v2 L hL hCard hMax
