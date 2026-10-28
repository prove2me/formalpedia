-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_completion_repair
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:31:10.326005+00:00
-- url     : https://prove2.me/submissions/7ad5100f-e136-4c4c-8a61-6eef73e9f6f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_edge_upper_bound_from_planar_drawing_repair_b095f50e
import Theorems.Thm_WilliamsonShmoys_maximal_completion_lower_bound_repair_b095f50e

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ U : SimpleGraph V,
      W ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ W) :
    3 * Fintype.card V = W.edgeSet.ncard + 6 := by
  have hUpper :
      W.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.edge_upper_bound_from_planar_drawing_repair_b095f50e W hV hW
  have hLower :
      3 * Fintype.card V ≤ W.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_completion_lower_bound_repair_b095f50e W hV hW hmax
  omega