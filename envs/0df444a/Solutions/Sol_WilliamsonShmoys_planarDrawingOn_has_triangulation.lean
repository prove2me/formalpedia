-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_has_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:43:37.53065+00:00
-- url     : https://prove2.me/submissions/6f06b50a-a831-4f18-92f2-337c5ff43d45
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_inclusionMaximalSupergraph
import Theorems.Thm_WilliamsonShmoys_inclusionMaximalPlanarDrawingOn_edgeCount

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hconn : L.Connected) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 = M.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planarDrawingOn_exists_inclusionMaximalSupergraph L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.inclusionMaximalPlanarDrawingOn_edgeCount M hV hM hmax⟩