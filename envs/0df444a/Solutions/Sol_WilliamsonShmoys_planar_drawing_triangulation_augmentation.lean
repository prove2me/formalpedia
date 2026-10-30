-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:53:03.461214+00:00
-- url     : https://prove2.me/submissions/becd18bb-c495-44f8-a2a8-8cbedd605c68

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_extension_for_triangulation
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_triangulation_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 ≤ Fintype.card V) :
    ∃ X : SimpleGraph V, W ≤ X ∧ WilliamsonShmoys.HasPlanarDrawingOn X ∧
      3 * Fintype.card V = X.edgeSet.ncard + 6 := by
  obtain ⟨X, hWX, hdrawX, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_drawable_extension_for_triangulation W hdraw
  have hcount :=
    WilliamsonShmoys.maximal_drawable_triangulation_edge_count X hdrawX hmax hV
  exact ⟨X, hWX, hdrawX, hcount⟩
