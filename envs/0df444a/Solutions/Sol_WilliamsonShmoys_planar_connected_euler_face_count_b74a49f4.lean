-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_euler_face_count_b74a49f4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:11:07.317579+00:00
-- url     : https://prove2.me/submissions/77b0b1c7-78ed-4733-9f9a-a1def00bdcbf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys
theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hConnected : K.Connected) (hCard : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 := by
  classical
  have h := hConnected.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (K.edgeSet).ncard = Nat.card K.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨K.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
