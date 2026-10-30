-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:59:34.947931+00:00
-- url     : https://prove2.me/submissions/6a7b9c73-df94-4f47-ba1d-3da90f3de3c4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_for_maximal_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hWdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V, W ≤ X →
      WilliamsonShmoys.HasPlanarDrawingOn X → X = W) :
    W.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hWT, hTdraw, hTcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_for_maximal_edge_count
      W hCard hWdraw
  have hEq : T = W := hmax T hWT hTdraw
  simpa [hEq] using hTcount