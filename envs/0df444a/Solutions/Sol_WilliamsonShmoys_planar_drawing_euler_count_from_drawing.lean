-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_count_from_drawing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T15:17:39.098874+00:00
-- url     : https://prove2.me/submissions/472cf6ac-adc3-4bfc-8e0a-90c5257efd4c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn


set_option autoImplicit false
open WilliamsonShmoys
theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected) : ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by
  classical
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (G.edgeSet).ncard = Nat.card G.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨G.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
