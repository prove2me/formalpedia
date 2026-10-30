-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_triangulation_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:33:42.448207+00:00
-- url     : https://prove2.me/submissions/4682fbf5-f3d5-4ab9-953f-ae1c0f172891

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_edge_upper_bound
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_maximal_edge_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V,
      T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_edge_upper_bound T hV hT
  · exact WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_maximal_edge_lower_bound T hV hT hmax