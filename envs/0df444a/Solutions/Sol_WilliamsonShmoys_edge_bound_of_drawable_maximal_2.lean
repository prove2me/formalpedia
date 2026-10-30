-- Prove2me | solution 2 for WilliamsonShmoys.edge_bound_of_drawable_maximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T10:01:49.096675+00:00
-- url     : https://prove2.me/submissions/17f79473-cd6a-4509-a19b-4fb0d98dccf5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound_from_completion

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  first
  | exact _root_.WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_from_completion
  | (apply _root_.WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_from_completion <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_from_completion <;> assumption)
