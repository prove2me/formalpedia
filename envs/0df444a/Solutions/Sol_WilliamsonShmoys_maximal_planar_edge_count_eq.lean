-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_eq
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:00:46.460318+00:00
-- url     : https://prove2.me/submissions/d36ad174-0896-48a6-8281-1ff9b643e66a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_count_upper_bound_ws
import Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_edge_count_lower_bound_ws

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M <= N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N <= M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_simple_edge_count_upper_bound_ws M hV hM
  · exact WilliamsonShmoys.maximal_planar_simple_edge_count_lower_bound_ws M hV hM hmax
