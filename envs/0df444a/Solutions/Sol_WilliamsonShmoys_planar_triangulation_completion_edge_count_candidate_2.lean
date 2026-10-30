-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulation_completion_edge_count_candidate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:09:51.42274+00:00
-- url     : https://prove2.me/submissions/f8b66147-8100-4290-bdf8-94ccea0dfe40

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_triangulated_completion_e8a894df

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_drawable_triangulated_completion_e8a894df
  | (apply _root_.WilliamsonShmoys.maximal_drawable_triangulated_completion_e8a894df <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_drawable_triangulated_completion_e8a894df <;> assumption)
