-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_for_maximal_drawable_graph_has_euler_edge_count_bbe69553_00c5_4ea0_b529_04641759cefa
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:14:41.200173+00:00
-- url     : https://prove2.me/submissions/fb5b55b0-f14d-4c2f-b1ef-783b8d0efcb5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_eq_euler

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  exact le_of_eq
    (WilliamsonShmoys.maximal_drawable_graph_edge_count_eq_euler
      K hK hcard hmax)