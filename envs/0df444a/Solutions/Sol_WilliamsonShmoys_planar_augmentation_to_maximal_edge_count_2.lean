-- Prove2me | solution 2 for WilliamsonShmoys.planar_augmentation_to_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:46:24.983266+00:00
-- url     : https://prove2.me/submissions/371f62fb-ddf9-4f83-9461-262f878b610a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count_candidate

set_option autoImplicit false
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
  | exact _root_.WilliamsonShmoys.planar_triangulation_completion_edge_count_candidate
  | (apply _root_.WilliamsonShmoys.planar_triangulation_completion_edge_count_candidate <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_triangulation_completion_edge_count_candidate <;> assumption)
