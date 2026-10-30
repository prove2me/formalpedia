-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count_fe58c870_e3e9_466f_b8e7_756f412ad0cc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:57:18.957052+00:00
-- url     : https://prove2.me/submissions/0660edc4-27a5-43aa-a1fc-23252abc5fe4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_exact_edge_count_for_f2fc27dd

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count_for_f2fc27dd
  | (apply _root_.WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count_for_f2fc27dd <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count_for_f2fc27dd <;> assumption)
