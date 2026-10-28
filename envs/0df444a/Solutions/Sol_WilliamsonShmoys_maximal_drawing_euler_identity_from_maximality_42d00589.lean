-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_euler_identity_from_maximality_42d00589
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:39:01.749527+00:00
-- url     : https://prove2.me/submissions/f995b4c6-08e0-4e27-b197-35a5cf05c1a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_connected_from_maximality
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_euler_identity_of_connected

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  have hConnected : K.Connected :=
    WilliamsonShmoys.maximal_drawing_connected_from_maximality K hK hmax hCard
  exact WilliamsonShmoys.maximal_drawing_euler_identity_of_connected
    K hK hmax hConnected hCard