-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_card_2d69255633d74159
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:55:51.559851+00:00
-- url     : https://prove2.me/submissions/84610b93-a5c3-402b-aa55-91808db85438
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_card_2d69255633d74159_planar_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_card_2d69255633d74159_maximality_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P.edgeSet ⊆ Q.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn Q → Q.edgeSet ⊆ P.edgeSet) :
    P.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.maximal_planar_card_2d69255633d74159_planar_upper_bound
      P hV hP
  · exact WilliamsonShmoys.maximal_planar_card_2d69255633d74159_maximality_lower_bound
      P hV hP hmax