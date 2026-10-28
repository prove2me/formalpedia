-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_exact_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:24:48.570679+00:00
-- url     : https://prove2.me/submissions/7d008ac2-0fc0-4c6a-b985-00b04b72724f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_exact_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_exact_edge_count_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L → False)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.maximal_drawable_graph_exact_edge_count_upper_bound K hK hCard
  · exact WilliamsonShmoys.maximal_drawable_graph_exact_edge_count_lower_bound K hK hMax hCard