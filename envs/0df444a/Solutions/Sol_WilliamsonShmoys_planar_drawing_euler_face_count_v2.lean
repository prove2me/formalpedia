-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:37:12.356212+00:00
-- url     : https://prove2.me/submissions/3127229c-6790-4bea-8b71-4fa6d16f88f4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hConnected : L.Connected) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 := by
  classical
  have h := hConnected.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (L.edgeSet).ncard = Nat.card L.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨L.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
