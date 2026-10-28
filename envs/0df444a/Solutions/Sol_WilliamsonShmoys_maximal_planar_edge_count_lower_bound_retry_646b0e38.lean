-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_retry_646b0e38
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:13:22.926963+00:00
-- url     : https://prove2.me/submissions/261ebfec-5c1e-4c06-bfe4-a33696bf532d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_completion_retry_646b0e38

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M <= N → WilliamsonShmoys.HasPlanarDrawingOn N → N <= M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hNcard⟩ :=
    WilliamsonShmoys.planar_graph_triangulation_completion_retry_646b0e38 M hV hM
  have hNM : N <= M := hmax N hMN hN
  have hEq : N = M := le_antisymm hNM hMN
  subst N
  exact hNcard.le