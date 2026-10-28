-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_drawingOn_connected_of_card_ge_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:44:16.959447+00:00
-- url     : https://prove2.me/submissions/df0c883b-6985-41e5-8896-041e61a0aad0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_of_disconnected

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    K.Connected := by
  by_contra hconn
  obtain ⟨L, hsub, hneq, hL⟩ :=
    WilliamsonShmoys.planar_extension_of_disconnected K hK hconn
  exact hneq (hmax L hsub hL)