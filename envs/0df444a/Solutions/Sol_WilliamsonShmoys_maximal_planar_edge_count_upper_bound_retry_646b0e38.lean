-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper_bound_retry_646b0e38
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:38:48.089934+00:00
-- url     : https://prove2.me/submissions/8e72584a-63be-4b4a-a7e6-0974bd5b49c1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M <= N → WilliamsonShmoys.HasPlanarDrawingOn N → N <= M) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  have heq := WilliamsonShmoys.maximal_planar_edge_count_eq M hV hM hmax
  omega