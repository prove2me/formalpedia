-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_formula_from_crossing_free_drawing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:30:35.732993+00:00
-- url     : https://prove2.me/submissions/5549c22f-a33b-43c1-a213-9aa7009f0655

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn


open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ F : ℕ, Fintype.card V + F = G.edgeSet.ncard + 2 := by
  classical
  have h := hConnected.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (G.edgeSet).ncard = Nat.card G.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨G.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
