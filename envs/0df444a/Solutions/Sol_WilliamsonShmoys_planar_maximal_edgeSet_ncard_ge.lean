-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edgeSet_ncard_ge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:28:43.723637+00:00
-- url     : https://prove2.me/submissions/59edff7d-3eae-454b-9181-d3c9f4311abf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_triangulation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hcard⟩ :=
    WilliamsonShmoys.planarDrawingOn_has_triangulation L hV hL hconn
  have hML : M ≤ L := hmax M hLM hM
  have hEq : M = L := le_antisymm hML hLM
  exact le_of_eq (by simpa [hEq] using hcard)