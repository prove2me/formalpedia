-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_formula_for_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:31:58.461279+00:00
-- url     : https://prove2.me/submissions/1cb1c18e-25a8-4027-bd29-b38ec6d751e6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false


open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ f : Nat, Fintype.card V + f = K.edgeSet.ncard + 2 := by
  classical
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (K.edgeSet).ncard = Nat.card K.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨K.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
