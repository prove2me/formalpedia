-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_96423339_d6c7_499e_a706_076681b42078
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:59:28.75636+00:00
-- url     : https://prove2.me/submissions/bc2a9ae9-2093-4f4d-9397-2d5c13da69e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_count_completion_nat

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ (M : SimpleGraph V), L ≤ M → HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hLK, hKDraw, hKCount⟩ :=
    WilliamsonShmoys.planar_drawing_has_edge_count_completion_nat L hDraw hCard
  have hKL : K = L := hMax K hLK hKDraw
  rw [hKL] at hKCount
  exact hKCount