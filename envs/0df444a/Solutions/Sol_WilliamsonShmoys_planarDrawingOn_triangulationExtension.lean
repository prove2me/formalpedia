-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_triangulationExtension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:35:52.535182+00:00
-- url     : https://prove2.me/submissions/a3a01855-8db5-4792-bc14-edc4cf848c96

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_maximal_extension_exists
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_from_extension_98d9ecda

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hDraw : HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V, U ≤ W ∧ HasPlanarDrawingOn W ∧
      W.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨W, hUW, hWDraw, hMax⟩ :=
    WilliamsonShmoys.planarDrawingOn_maximal_extension_exists U hDraw
  refine ⟨W, hUW, hWDraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawingOn_edge_count_from_extension_98d9ecda
    W hWDraw hCard hMax
