-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_6274f47d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:26:02.354967+00:00
-- url     : https://prove2.me/submissions/ba16bed3-ff0d-41d1-86dc-47a928703fc7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_has_triangulated_supergraph_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet = M.edgeSet) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hNcard⟩ :=
    WilliamsonShmoys.planarDrawing_has_triangulated_supergraph_edge_count M hM hCard
  have hNM : N.edgeSet = M.edgeSet := hMax N hMN hN
  calc
    M.edgeSet.ncard = N.edgeSet.ncard := by rw [← hNM]
    _ = 3 * Fintype.card V - 6 := hNcard