-- Prove2me | solution 1 for WilliamsonShmoys.connected_face_count_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:24:00.557997+00:00
-- url     : https://prove2.me/submissions/e5365b14-8fe5-46dc-8e8f-641ca427188f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hconn : G.Connected) :
    Fintype.card V ≤ G.edgeSet.ncard + 1 := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rwa [Nat.card_eq_fintype_card] at h
