-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count__p2m_6294dfb9_01c6_44e4_b6a8_a896c7d41add_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:26:20.077332+00:00
-- url     : https://prove2.me/submissions/611addca-082c-4548-93a0-bb87fc5759b8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hConnected : J.Connected) :
    ∃ f : ℕ, Fintype.card V + f = J.edgeSet.ncard + 2 := by
  have h := hConnected.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
  exact ⟨J.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
