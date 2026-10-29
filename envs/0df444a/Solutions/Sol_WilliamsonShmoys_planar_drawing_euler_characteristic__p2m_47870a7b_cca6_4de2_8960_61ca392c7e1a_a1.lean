-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_characteristic__p2m_47870a7b_cca6_4de2_8960_61ca392c7e1a_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:17:35.621822+00:00
-- url     : https://prove2.me/submissions/f2c17f66-2f5e-489c-8110-4eee7e475ea8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hconn : K.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ F : ℕ, Fintype.card V + F = K.edgeSet.ncard + 2 := by
  have h := (hconn).card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
  exact ⟨K.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
