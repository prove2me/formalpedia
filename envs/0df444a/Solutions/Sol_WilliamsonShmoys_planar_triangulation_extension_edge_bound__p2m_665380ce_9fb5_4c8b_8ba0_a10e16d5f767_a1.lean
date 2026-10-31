-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_edge_bound__p2m_665380ce_9fb5_4c8b_8ba0_a10e16d5f767_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:32:49.695343+00:00
-- url     : https://prove2.me/submissions/56dfe8b4-3104-4605-b2aa-8f8d5315760c

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_v2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_v2 G hG hV
