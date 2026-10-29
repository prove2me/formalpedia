-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_for_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T01:46:08.032885+00:00
-- url     : https://prove2.me/submissions/6cd26dcd-2100-4f28-8625-b21a7ff46d13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_at_least_three_vertices__p2m_e0ba5d4e_e2d8_4da4_a9bb_b103b70f3cfe_a5
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_e0ba5d4e_e2d8_4da4_a9bb_b103b70f3cfe_a5

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V)
    (hmax : forall R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R ->
      Set.Subset Q.edgeSet R.edgeSet -> Set.Subset R.edgeSet Q.edgeSet) :
    Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hup := WilliamsonShmoys.planar_edge_count_upper_bound_for_at_least_three_vertices__p2m_e0ba5d4e_e2d8_4da4_a9bb_b103b70f3cfe_a5 Q hdraw hV
  have hlo := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e0ba5d4e_e2d8_4da4_a9bb_b103b70f3cfe_a5 Q hdraw hV hmax
  omega