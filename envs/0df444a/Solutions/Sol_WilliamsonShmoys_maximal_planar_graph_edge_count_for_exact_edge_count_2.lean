-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_edge_count_for_exact_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T10:16:44.972803+00:00
-- url     : https://prove2.me/submissions/84214b9d-a68f-46c6-97d7-e6400605af7a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_e8a894df

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_drawable_edge_count_e8a894df
  | (apply _root_.WilliamsonShmoys.maximal_drawable_edge_count_e8a894df <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_drawable_edge_count_e8a894df <;> assumption)
