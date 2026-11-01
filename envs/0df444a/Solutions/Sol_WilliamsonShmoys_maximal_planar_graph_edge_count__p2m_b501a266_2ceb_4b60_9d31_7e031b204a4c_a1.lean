-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b501a266_2ceb_4b60_9d31_7e031b204a4c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:57:46.978254+00:00
-- url     : https://prove2.me/submissions/26403d8e-7a08-4d63-a6ae-9ee28a9a1a8f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_edge_count__p2m_33d20c1e_677c_47dc_9e82_8d3a28e57fca_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hNcard⟩ :=
    WilliamsonShmoys.planar_extension_edge_count__p2m_33d20c1e_677c_47dc_9e82_8d3a28e57fca_a1
      M hM hcard
  have hNM := hMax N hMN hN
  have heq : M.edgeSet = N.edgeSet := Set.Subset.antisymm hMN hNM
  rw [← heq] at hNcard
  omega