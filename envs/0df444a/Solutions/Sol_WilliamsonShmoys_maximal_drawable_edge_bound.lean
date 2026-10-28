-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:08:14.025416+00:00
-- url     : https://prove2.me/submissions/8101e81f-5a8f-4624-84e7-3916f07a2840
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_below_maximal_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hMax : ∀ W : SimpleGraph V, U ≤ W →
      WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ U) :
    3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by
  by_contra hTarget
  have hGap : U.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨W, hUW, hNotWU, hW⟩ :=
    WilliamsonShmoys.planar_extension_below_maximal_edge_bound U hV hU hGap
  exact hNotWU (hMax W hUW hW)