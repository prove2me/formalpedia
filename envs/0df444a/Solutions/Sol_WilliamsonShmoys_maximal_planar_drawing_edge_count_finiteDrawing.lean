-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_finiteDrawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:23:26.20299+00:00
-- url     : https://prove2.me/submissions/dc76f3e5-ddcc-4bb1-9ec2-b7cbadc578ae

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_augmentation

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ X : SimpleGraph V, W ≤ X →
      WilliamsonShmoys.HasPlanarDrawingOn X → X = W) :
    3 * Fintype.card V = W.edgeSet.ncard + 6 := by
  obtain ⟨X, hWX, hXdraw, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_augmentation W hdraw hV
  have hXW : X = W := hmax X hWX hXdraw
  rw [← hXW]
  exact hcount