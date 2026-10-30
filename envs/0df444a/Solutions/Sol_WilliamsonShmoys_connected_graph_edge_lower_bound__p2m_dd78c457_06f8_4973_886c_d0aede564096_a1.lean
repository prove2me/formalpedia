-- Prove2me | solution 1 for WilliamsonShmoys.connected_graph_edge_lower_bound__p2m_dd78c457_06f8_4973_886c_d0aede564096_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:52:43.405491+00:00
-- url     : https://prove2.me/submissions/2f3555c4-7a6a-40c1-8c5f-8d7c84ddb896

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (hconn : H.Connected) :
    Fintype.card V ≤ H.edgeSet.ncard + 1 := by
  simpa only [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
    hconn.card_vert_le_card_edgeSet_add_one