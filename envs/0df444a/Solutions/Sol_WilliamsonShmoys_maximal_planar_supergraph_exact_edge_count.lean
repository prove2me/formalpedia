-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_supergraph_exact_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:47:40.119379+00:00
-- url     : https://prove2.me/submissions/a88d26ff-ea09-4404-9a0c-3fb9ccae41b5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_finite_maximality
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_finite_maximality M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_planar_triangulation_edge_count N hV hN hmax⟩