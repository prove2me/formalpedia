-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_edge_count_e9ce3df1_a197_4828_a24c_84c363604464
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:16:13.861097+00:00
-- url     : https://prove2.me/submissions/69864f8c-3c34-48de-837f-9c5db9cc9ffa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.maximal_drawing_edge_count_lower_bound L hV hL hmax
  · exact WilliamsonShmoys.maximal_drawing_edge_count_upper_bound L hV hL