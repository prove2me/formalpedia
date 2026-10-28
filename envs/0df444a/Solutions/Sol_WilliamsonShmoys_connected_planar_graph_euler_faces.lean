-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_graph_euler_faces
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:37:27.304747+00:00
-- url     : https://prove2.me/submissions/1f87fd8a-606d-4398-bacc-5c62a1d03790

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ F : ℕ, Fintype.card V + F = Y.edgeSet.ncard + 2 := by
  classical
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (Y.edgeSet).ncard = Nat.card Y.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨Y.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
