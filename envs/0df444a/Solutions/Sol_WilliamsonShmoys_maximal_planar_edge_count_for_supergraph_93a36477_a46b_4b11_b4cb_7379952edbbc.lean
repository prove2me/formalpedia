-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_supergraph_93a36477_a46b_4b11_b4cb_7379952edbbc
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:24:17.537186+00:00
-- url     : https://prove2.me/submissions/d2c1d8c1-a406-4188-a865-bbdaf5b36863

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound_retry_646b0e38
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_retry_646b0e38

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M <= N → WilliamsonShmoys.HasPlanarDrawingOn N → N <= M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  have hupper : M.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_edge_count_upper_bound_retry_646b0e38 M hV hM hmax
  have hlower : 3 * Fintype.card V <= M.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound_retry_646b0e38 M hV hM hmax
  exact Nat.le_antisymm hlower hupper