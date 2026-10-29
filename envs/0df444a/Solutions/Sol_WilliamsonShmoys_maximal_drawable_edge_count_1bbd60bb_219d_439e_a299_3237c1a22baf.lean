-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_1bbd60bb_219d_439e_a299_3237c1a22baf
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:12:49.405013+00:00
-- url     : https://prove2.me/submissions/95f48573-d9bf-4ace-b0dd-f9a60d93d642

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_full_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.drawable_supergraph_full_edge_count L hV hL
  have hEq : M = L := hmax M hLM hM
  subst M
  exact hcount