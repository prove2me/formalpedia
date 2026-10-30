-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:28:21.185733+00:00
-- url     : https://prove2.me/submissions/b6e1574e-e663-4ff2-b315-55ca40cf25fc

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_repair2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, G ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ G) :
    3 * Fintype.card V - 6 ≤ G.edgeSet.ncard := by
  obtain ⟨N, hGN, hN, hNcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_repair2 G hG hV
  have hNG : N ≤ G := hMax N hGN hN
  have hEq : N = G := le_antisymm hNG hGN
  have hGcard : G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    simpa [hEq] using hNcard
  omega