-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_for_edge_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:33:16.091698+00:00
-- url     : https://prove2.me/submissions/3577a684-be59-4d9a-ae32-ecb5b194a5a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_upper_bound_repair_8fa97b2b
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound_repair_8fa97b2b

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M.edgeSet ⊂ N.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn N) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper : M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_upper_bound_repair_8fa97b2b M hV hM
  have hlower : 3 * Fintype.card V - 6 ≤ M.edgeSet.ncard :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_repair_8fa97b2b M hV hM hmax
  omega