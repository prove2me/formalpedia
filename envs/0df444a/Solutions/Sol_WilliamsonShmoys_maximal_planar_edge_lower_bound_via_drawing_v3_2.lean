-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower_bound_via_drawing_v3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:53:23.461128+00:00
-- url     : https://prove2.me/submissions/39b76661-d43d-4d66-a833-db8460d5bff7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound_retry_20261027__p2m_82d3f981_edc6_4261_adff_4cb68e598032_a5

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_retry_20261027__p2m_82d3f981_edc6_4261_adff_4cb68e598032_a5
  | (apply _root_.WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_retry_20261027__p2m_82d3f981_edc6_4261_adff_4cb68e598032_a5 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_retry_20261027__p2m_82d3f981_edc6_4261_adff_4cb68e598032_a5 <;> assumption)
