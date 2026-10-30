-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_for_edge_bound_9f95e338
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:42:55.722658+00:00
-- url     : https://prove2.me/submissions/0498d8cc-3ad6-49dd-9506-a256e985c0ed

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_bound_9f95e338
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_edge_bound_9f95e338

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, H ≤ T ∧ HasPlanarDrawingOn T ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hHT, hTdraw, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_bound_9f95e338 H hdraw
  exact ⟨T, hHT, hTdraw,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_bound_9f95e338 T hTdraw hV hmax⟩