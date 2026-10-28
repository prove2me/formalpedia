-- Prove2me | solution 2 for WilliamsonShmoys.edge_maximal_drawingOn_connected_of_card_ge_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:43:01.239777+00:00
-- url     : https://prove2.me/submissions/76170ad2-3b06-488e-ad9c-e4839a698dc8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_of_disconnected_of_card_ge_three

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
    WilliamsonShmoys.planar_extension_of_disconnected_of_card_ge_three
      K hK hV hconn
  exact hneq (hmax L hsub hL)