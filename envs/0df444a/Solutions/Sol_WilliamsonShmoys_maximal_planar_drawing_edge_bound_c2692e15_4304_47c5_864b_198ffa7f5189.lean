-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound_c2692e15_4304_47c5_864b_198ffa7f5189
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:58:02.834289+00:00
-- url     : https://prove2.me/submissions/e86e65bd-d0e4-458a-b8ba-fd856e310692
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_triangulation_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ Z : SimpleGraph V, W ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z ≤ W) :
    3 * Fintype.card V ≤ W.edgeSet.ncard + 6 := by
  obtain ⟨Z, hWZ, hZ, hcard⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_edge_bound_triangulation_extension
      W hV hW
  have hZW : Z ≤ W := hmax Z hWZ hZ
  have hEq : W = Z := le_antisymm hWZ hZW
  rw [hEq]
  exact le_of_eq hcard