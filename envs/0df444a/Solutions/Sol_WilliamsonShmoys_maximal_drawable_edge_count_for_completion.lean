-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_for_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:26:55.339252+00:00
-- url     : https://prove2.me/submissions/90712c79-41ab-44b4-9f26-171e30227b01

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hMdraw : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hNdraw, hNcard⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulated_supergraph M hMdraw hCard
  have hNM : N ≤ M := hMmax N hMN hNdraw
  have hEq : N = M := le_antisymm hNM hMN
  simpa [hEq] using hNcard