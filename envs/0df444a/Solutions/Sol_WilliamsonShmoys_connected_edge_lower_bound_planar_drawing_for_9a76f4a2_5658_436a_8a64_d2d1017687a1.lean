-- Prove2me | solution 1 for WilliamsonShmoys.connected_edge_lower_bound_planar_drawing_for_9a76f4a2_5658_436a_8a64_d2d1017687a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T03:02:03.618067+00:00
-- url     : https://prove2.me/submissions/fae249fe-4f0a-4cee-8f8d-939b85b34652

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hconn : L.Connected) :
    Fintype.card V - 1 <= L.edgeSet.ncard := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
  omega
