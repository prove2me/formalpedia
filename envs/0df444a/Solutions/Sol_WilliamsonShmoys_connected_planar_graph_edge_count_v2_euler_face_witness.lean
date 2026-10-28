-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_graph_edge_count_v2_euler_face_witness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T04:14:11.434911+00:00
-- url     : https://prove2.me/submissions/92d3c6e3-e776-495c-925d-fc0542f46742

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ f : ℕ, Fintype.card V + f = Y.edgeSet.ncard + 2 := by
  classical
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (Y.edgeSet).ncard = Nat.card Y.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨Y.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
