-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count_afa305d5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:02:00.655656+00:00
-- url     : https://prove2.me/submissions/3df77fdd-a2a3-49dc-8107-dcb1a95143e6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hConn : H.Connected) :
    exists f : Nat, Fintype.card V + f = H.edgeSet.ncard + 2 := by
  have h := hConn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
  exact ⟨H.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
