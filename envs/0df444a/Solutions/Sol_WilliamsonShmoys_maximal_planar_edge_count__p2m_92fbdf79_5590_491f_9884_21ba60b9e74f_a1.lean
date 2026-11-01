-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_92fbdf79_5590_491f_9884_21ba60b9e74f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:34:32.102202+00:00
-- url     : https://prove2.me/submissions/939a91d5-3451-4f31-bf51-8efa0e37c842
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_76f2d72e_f140_4cd7_bf10_fd0bb7e9203e_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_76f2d72e_f140_4cd7_bf10_fd0bb7e9203e_a2

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_76f2d72e_f140_4cd7_bf10_fd0bb7e9203e_a2 H hcard hH
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_76f2d72e_f140_4cd7_bf10_fd0bb7e9203e_a2 H hcard hH hmax
  omega