-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_count_for_face_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:20:05.75345+00:00
-- url     : https://prove2.me/submissions/9a247089-55e1-4421-9c64-24f1343e5d6f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 := by
  classical
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (K.edgeSet).ncard = Nat.card K.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨K.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
