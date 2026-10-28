-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:06:38.170975+00:00
-- url     : https://prove2.me/submissions/225bc584-d895-4add-ade4-484ca6e039a8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ f : ℕ, K.edgeSet.ncard + 2 = Fintype.card V + f := by
  have hcard := hconn.card_vert_le_card_edgeSet_add_one
  have hle : Fintype.card V ≤ K.edgeSet.ncard + 1 := by
    simpa [Set.ncard] using hcard
  refine ⟨K.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega