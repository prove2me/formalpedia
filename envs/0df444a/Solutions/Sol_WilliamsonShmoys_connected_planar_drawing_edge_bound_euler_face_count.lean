-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound_euler_face_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:21:24.958394+00:00
-- url     : https://prove2.me/submissions/c26422ce-5c3f-413d-8335-f332fc529227

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false


open WilliamsonShmoys
theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hConn : G.Connected) : ∃ f : ℕ, G.edgeSet.ncard + 2 = Fintype.card V + f := by
  classical
  have h := hConn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (G.edgeSet).ncard = Nat.card G.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨G.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
