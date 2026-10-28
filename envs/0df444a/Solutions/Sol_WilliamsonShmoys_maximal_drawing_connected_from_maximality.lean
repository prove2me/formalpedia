-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_connected_from_maximality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:57:55.720397+00:00
-- url     : https://prove2.me/submissions/a90f8698-6d77-4c1b-b9cd-35d2e4594af5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_disconnected_has_strict_planar_extension

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
    K.Connected := by
  by_contra hconn
  obtain ⟨L, hstrict, hL⟩ :=
    WilliamsonShmoys.drawable_disconnected_has_strict_planar_extension K hK hCard hconn
  exact hstrict.2 (hmax L hstrict.1 hL)