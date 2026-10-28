-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_completion_44ee6346_c5c8_4937_ab77_ca51e02cb099
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:41:14.555975+00:00
-- url     : https://prove2.me/submissions/2e4fb0af-a825-4b2c-b7dd-742ab6f20662
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_extend_to_inclusion_maximal
import Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      Set.Subset G.edgeSet H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.planarDrawing_extend_to_inclusion_maximal G hG
  exact ⟨H, hGH, hH,
    WilliamsonShmoys.inclusion_maximal_planar_edge_count H hV hH hMax⟩