-- Prove2me | solution 2 for WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_graph_for_f2fc27dd
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:10:24.770349+00:00
-- url     : https://prove2.me/submissions/469d8810-3d51-4acc-b660-ede2a132f1d9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_e8a894df

set_option autoImplicit false

open WilliamsonShmoys
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
