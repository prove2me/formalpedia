-- Prove2me | solution 2 for WilliamsonShmoys.connected_card_le_edge_ncard_add_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:23:53.295783+00:00
-- url     : https://prove2.me/submissions/abe27916-91ae-48c1-97ad-6c96b2a53be1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hconn : L.Connected) :
    Fintype.card V ≤ L.edgeSet.ncard + 1 := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rwa [Nat.card_eq_fintype_card] at h
