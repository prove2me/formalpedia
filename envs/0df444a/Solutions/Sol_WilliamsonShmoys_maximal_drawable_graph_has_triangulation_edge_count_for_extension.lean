-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_for_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:36:25.621872+00:00
-- url     : https://prove2.me/submissions/672f6fee-9065-4ee3-a83e-ebf59283e38c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulation_extension_for_maximality
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulation_extension_for_maximality
      L hV hL
  have hML : M ≤ L := hmax M hLM hM
  have hEq : M = L := le_antisymm hML hLM
  simpa [hEq] using hcount