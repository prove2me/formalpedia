-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_maximal_planar_lower_retry3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T14:04:39.095097+00:00
-- url     : https://prove2.me/submissions/1f308cba-8185-4240-8086-ab1fff886592
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_triangulationExtension

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hDraw : HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ W : SimpleGraph V, U ≤ W → HasPlanarDrawingOn W → W = U) :
    3 * Fintype.card V - 6 ≤ U.edgeSet.ncard := by
  obtain ⟨W, hUW, hDrawW, hCount⟩ :=
    WilliamsonShmoys.planarDrawingOn_triangulationExtension U hDraw hCard
  have hWU : W = U := hMax W hUW hDrawW
  rw [← hWU]
  exact Nat.le_of_eq hCount.symm