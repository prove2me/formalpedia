-- Prove2me | solution 1 for WilliamsonShmoys.card_eq_three_n_sub_six_of_planar_maximal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:51:36.503743+00:00
-- url     : https://prove2.me/submissions/ee8148c1-1ec7-4a91-a7ac-42b7a1240aaf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_from_drawing
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_lower_bound_from_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_edge_upper_bound_from_drawing H hV hH
  · exact WilliamsonShmoys.planar_maximal_edge_lower_bound_from_drawing H hV hH hMax
