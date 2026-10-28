-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:53:51.368806+00:00
-- url     : https://prove2.me/submissions/9741a421-09c1-4a7e-bd9b-063fbc5f88f3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ, G.edgeSet.ncard + 2 = Fintype.card V + f := by
  have h := hConnected.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
  exact ⟨G.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
