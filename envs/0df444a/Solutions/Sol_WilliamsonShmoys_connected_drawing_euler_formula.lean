-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_euler_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:36:51.87782+00:00
-- url     : https://prove2.me/submissions/77b36f6d-b9e5-4152-8220-ef0ddcbe1b47

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by
  classical
  have h := hConn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (G.edgeSet).ncard = Nat.card G.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨G.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
