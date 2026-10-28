-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_on_euler_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:51:18.254796+00:00
-- url     : https://prove2.me/submissions/c3baf416-6ec4-482d-927b-c9ff75b2896a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_7bfae1f5

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hU : HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ W : SimpleGraph V, HasPlanarDrawingOn W →
      (∀ u v, U.Adj u v → W.Adj u v) → W = U) :
    3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by
  obtain ⟨W, hW, hUW, hEdge⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_7bfae1f5 U hU hCard
  have hWU : W = U := hMax W hW hUW
  rw [← hWU]
  exact le_of_eq hEdge.symm