-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_repair2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:55:20.862369+00:00
-- url     : https://prove2.me/submissions/0a697727-64f8-4a74-9373-9859d35bfaa3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_maximal_extension_repair2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_repair2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      G ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hGN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_on_maximal_extension_repair2 G hG hV
  refine ⟨N, hGN, hN, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count_repair2 N hN hmax hV