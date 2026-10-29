-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_edge_lower_bound_16efa91f_ea17_4fca_8681_329f091064c3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:39:51.074817+00:00
-- url     : https://prove2.me/submissions/6f4f8b78-9192-4e14-ad0c-6146e7303011

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exact_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨N, hMN, hN, hCount⟩ :=
    WilliamsonShmoys_maximal_planar_supergraph_exact_edge_count M hV hM
  have hEq : N = M := hMax N hMN hN
  rw [hEq] at hCount
  omega