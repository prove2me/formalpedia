-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_formula_7c5eea9e
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:49:52.747987+00:00
-- url     : https://prove2.me/submissions/d5f21138-f3e5-4383-b4c2-e6c48548170f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ F : ℕ, Fintype.card V + F = K.edgeSet.ncard + 2 := by
  classical
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (K.edgeSet).ncard = Nat.card K.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨K.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
