-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count_from_embedding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:53:53.893712+00:00
-- url     : https://prove2.me/submissions/5bf3ee8e-4e13-4b61-b935-8cb17596d818

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
  exact ⟨G.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
