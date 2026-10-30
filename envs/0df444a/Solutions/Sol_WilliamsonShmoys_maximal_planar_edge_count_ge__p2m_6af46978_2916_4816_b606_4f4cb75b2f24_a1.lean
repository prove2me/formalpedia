-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_ge__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:09:15.096021+00:00
-- url     : https://prove2.me/submissions/c681cfd9-7803-47dc-a4e7-271d1f309abc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_for_maximal_count_957bde25
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V,
      L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    3 * Fintype.card V - 6 <= L.edgeSet.ncard := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_for_maximal_count_957bde25
  | (apply _root_.WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_for_maximal_count_957bde25 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_for_maximal_count_957bde25 <;> assumption)
