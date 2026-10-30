-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_98108dba_1927_4e81_b6e3_ce95ad278038
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:23:58.875504+00:00
-- url     : https://prove2.me/submissions/d105bdfb-7865-4e31-8e8c-0733334984d7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_98108dba_1927_4e81_b6e3_ce95ad278038_planar_completion
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_98108dba_1927_4e81_b6e3_ce95ad278038_planar_completion
      L hV hL
  have hML : M = L := hmax M hLM hM
  simpa [hML] using hcount