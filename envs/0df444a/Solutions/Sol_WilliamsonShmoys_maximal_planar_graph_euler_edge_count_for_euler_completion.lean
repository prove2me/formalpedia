-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_euler_edge_count_for_euler_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:59:04.664776+00:00
-- url     : https://prove2.me/submissions/fde2f419-840c-4174-be42-0aca599f72ae

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound_via_euler_a4779231
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_via_triangulation_a4779231

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.maximal_planar_edge_count_upper_bound_via_euler_a4779231 K hV hK
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_via_triangulation_a4779231 K hV hK hMax
  omega