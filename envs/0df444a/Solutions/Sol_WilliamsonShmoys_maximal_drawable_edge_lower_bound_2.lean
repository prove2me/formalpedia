-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:14:50.674619+00:00
-- url     : https://prove2.me/submissions/962430d3-7ae3-40f3-a141-293560867d79

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2
  | (apply _root_.WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2 <;> assumption)
