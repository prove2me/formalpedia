-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_triangulation_extension_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:27:51.042244+00:00
-- url     : https://prove2.me/submissions/b916e98c-dab9-4452-ab82-5c46da1ec788

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension_v2_aux
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_v2_aux

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hV : 3 <= Fintype.card V) :
    ∃ W : SimpleGraph V,
      (∀ {u v}, U.Adj u v → W.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      W.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨W, hUW, hWdraw, hmax⟩ :=
    WilliamsonShmoys.planar_drawingOn_maximal_extension_v2_aux U hdraw
  refine ⟨W, hUW, hWdraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count_v2_aux W hWdraw hV hmax