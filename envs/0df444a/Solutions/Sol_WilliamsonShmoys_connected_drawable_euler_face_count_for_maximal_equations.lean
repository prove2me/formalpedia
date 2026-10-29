-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawable_euler_face_count_for_maximal_equations
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:19:08.768726+00:00
-- url     : https://prove2.me/submissions/1055ff26-9e30-4c9e-9c1a-cc7a2e6f884e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hConnected : L.Connected) : ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 := by
  have h := (hConnected).card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
  exact ⟨L.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
