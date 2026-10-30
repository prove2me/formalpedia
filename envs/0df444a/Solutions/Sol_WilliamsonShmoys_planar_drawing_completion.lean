-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:05:47.706836+00:00
-- url     : https://prove2.me/submissions/2f8bd3db-ff3a-47af-a7d6-23259f9ae641

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_exists_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_upper_bound
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_maximal_edge_lower_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hGK, hPlanar, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_completion_exists_maximal_extension G hDrawing
  have hUpper :=
    WilliamsonShmoys.planar_drawing_completion_edge_upper_bound K hPlanar hV
  have hLower :=
    WilliamsonShmoys.planar_drawing_completion_maximal_edge_lower_bound K hPlanar hMax hV
  refine ⟨K, hGK, hPlanar, ?_⟩
  omega