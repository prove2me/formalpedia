-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count_7c1cdf82
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:44:51.940745+00:00
-- url     : https://prove2.me/submissions/19c45464-5ed1-45f5-af0c-ac4da8b0c3d3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hconn : H.Connected) : Exists fun f : Nat => Fintype.card V + f = H.edgeSet.ncard + 2 := by
  classical
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (H.edgeSet).ncard = Nat.card H.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨H.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
