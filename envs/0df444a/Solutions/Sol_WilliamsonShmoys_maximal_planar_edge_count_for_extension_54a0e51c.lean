-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_extension_54a0e51c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:22:48.488999+00:00
-- url     : https://prove2.me/submissions/7da9a6f3-3ae5-4229-9415-a54d66d60e2e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_extension_54a0e51c

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hMax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet ⊆ L.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.exists_planar_edge_count_extension_54a0e51c L hL hV
  have hML : M.edgeSet ⊆ L.edgeSet := hMax M hLM hM
  have hEq : L.edgeSet = M.edgeSet := Set.Subset.antisymm hLM hML
  simpa [hEq] using hcount