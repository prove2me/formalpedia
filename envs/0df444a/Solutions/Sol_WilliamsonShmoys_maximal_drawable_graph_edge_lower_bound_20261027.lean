-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_20261027
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:14:54.234275+00:00
-- url     : https://prove2.me/submissions/119deede-3c22-487c-a20e-88645967ba32

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound_retry_20261027__p2m_82d3f981_edc6_4261_adff_4cb68e598032_a5

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_retry_20261027__p2m_82d3f981_edc6_4261_adff_4cb68e598032_a5
  | (apply _root_.WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_retry_20261027__p2m_82d3f981_edc6_4261_adff_4cb68e598032_a5 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_retry_20261027__p2m_82d3f981_edc6_4261_adff_4cb68e598032_a5 <;> assumption)
