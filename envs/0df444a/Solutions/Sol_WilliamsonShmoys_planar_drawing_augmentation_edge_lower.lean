-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmentation_edge_lower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:44:13.309051+00:00
-- url     : https://prove2.me/submissions/9d5026c3-9518-451b-b388-f0a82a262ec4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph_c2692e15_4304_47c5_864b_198ffa7f5189
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_c2692e15_4304_47c5_864b_198ffa7f5189

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      U ≤ W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      3 * Fintype.card V ≤ W.edgeSet.ncard + 6 := by
  obtain ⟨W, hUW, hW, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_c2692e15_4304_47c5_864b_198ffa7f5189 U hU
  exact ⟨W, hUW, hW,
    WilliamsonShmoys.maximal_planar_drawing_edge_bound_c2692e15_4304_47c5_864b_198ffa7f5189 W hV hW hmax⟩