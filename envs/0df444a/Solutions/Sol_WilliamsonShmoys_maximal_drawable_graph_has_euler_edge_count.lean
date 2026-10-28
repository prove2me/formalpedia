-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:08:14.427605+00:00
-- url     : https://prove2.me/submissions/46b8eb1a-b3e0-45cb-a46c-b96a41eae80e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_edge_count_upper_bound_for_maximal_drawable_graph_has_euler_edge_count_bbe69553_00c5_4ea0_b529_04641759cefa
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound_for_maximal_drawable_graph_has_euler_edge_count_bbe69553_00c5_4ea0_b529_04641759cefa

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.drawable_edge_count_upper_bound_for_maximal_drawable_graph_has_euler_edge_count_bbe69553_00c5_4ea0_b529_04641759cefa K hK hcard
  have hlower := WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_for_maximal_drawable_graph_has_euler_edge_count_bbe69553_00c5_4ea0_b529_04641759cefa K hK hcard hmax
  omega