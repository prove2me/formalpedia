-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_maximal_edge_saturation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:56:28.986906+00:00
-- url     : https://prove2.me/submissions/12b58994-795c-4de8-9aa4-5b747f06b7a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_for_maximal_edge_saturation_fa75ef82

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hDrawM, hExact⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion_for_maximal_edge_saturation_fa75ef82
      L hDraw hCard
  have hEq : M = L := hMax M hLM hDrawM
  have hLExact : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    simpa [hEq] using hExact
  omega