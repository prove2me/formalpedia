-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_00187ed1_118c_4569_ae21_cc59aa929691
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:40:10.617986+00:00
-- url     : https://prove2.me/submissions/9c621fe6-4985-4441-b578-4e26c9249700

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_exact_edge_count_9ac50290_da1b_42d2_8798_1bec9d81b4c1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = L.edgeSet) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hsub, hM, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_supergraph_exact_edge_count_9ac50290_da1b_42d2_8798_1bec9d81b4c1 L hL hV
  have heq : M.edgeSet = L.edgeSet := hmax M hsub hM
  simpa [heq] using hcount