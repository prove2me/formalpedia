-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_extension_9c238260_8e64_40d3_b87d_42af728950e9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:44:14.556862+00:00
-- url     : https://prove2.me/submissions/384bc8c4-280a-41b9-b2c1-81f3422c2fc9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_extension

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDrawing : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H := by
  classical
  obtain ⟨H, hGH, hDrawable, hCard, hMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_extension
      (P := HasPlanarDrawingOn) G hDrawing
  exact ⟨H, hGH, hCard, hDrawable, hMax⟩