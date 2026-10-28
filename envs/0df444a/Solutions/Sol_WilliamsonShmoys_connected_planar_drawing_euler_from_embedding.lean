-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_from_embedding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:15:32.28622+00:00
-- url     : https://prove2.me/submissions/e2688cb2-2703-4ec5-8fe7-3def54f01e38

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn


open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G) :
    ∃ f : ℕ, G.edgeSet.ncard + 2 = Fintype.card V + f := by
  classical
  have h := hConn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (G.edgeSet).ncard = Nat.card G.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨G.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
