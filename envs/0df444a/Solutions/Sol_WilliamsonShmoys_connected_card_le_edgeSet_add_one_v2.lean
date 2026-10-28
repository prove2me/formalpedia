-- Prove2me | solution 1 for WilliamsonShmoys.connected_card_le_edgeSet_add_one_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:38:42.63414+00:00
-- url     : https://prove2.me/submissions/8b73a7b8-6025-4524-afab-67c87281d1c7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hConnected : L.Connected) :
    Fintype.card V ≤ L.edgeSet.ncard + 1 := by
  have h := hConnected.card_vert_le_card_edgeSet_add_one
  rwa [Nat.card_eq_fintype_card] at h
