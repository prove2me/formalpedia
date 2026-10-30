-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound__p2m_30825c49_c1ed_4d16_b870_dd4c24d4c0d7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:10:49.263331+00:00
-- url     : https://prove2.me/submissions/638d84eb-7588-4776-a9e3-1c5f6c450b6c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_62da979b_c365_4bf4_9e37_d6d269befee9_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet →
      HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_62da979b_c365_4bf4_9e37_d6d269befee9_a2
      M hM hCard
  have hNM : N = M := hmax N hMN hN
  exact le_of_eq (by simpa [hNM] using hcount.symm)