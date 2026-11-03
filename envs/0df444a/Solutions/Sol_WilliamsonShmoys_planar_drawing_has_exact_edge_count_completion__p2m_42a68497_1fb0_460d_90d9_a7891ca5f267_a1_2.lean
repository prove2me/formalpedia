-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_42a68497_1fb0_460d_90d9_a7891ca5f267_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:26:01.310452+00:00
-- url     : https://prove2.me/submissions/9d9feb15-10c5-41d9-8a09-e3c9898710cd

import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      Set.Subset G.edgeSet K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_completion_edge_count__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5 G hG hV