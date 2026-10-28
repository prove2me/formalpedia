-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_for_face_accounting_57972424
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:36:35.429751+00:00
-- url     : https://prove2.me/submissions/f3edd35b-9ad9-42c5-bd56-131ad4330950

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected) :
    Exists (fun f : Nat => Fintype.card V + f = G.edgeSet.ncard + 2) := by
  classical
  have h := hConn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (G.edgeSet).ncard = Nat.card G.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨G.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
