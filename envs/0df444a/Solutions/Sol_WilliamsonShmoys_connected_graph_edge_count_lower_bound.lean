-- Prove2me | solution 1 for WilliamsonShmoys.connected_graph_edge_count_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:23:48.12693+00:00
-- url     : https://prove2.me/submissions/d99fe027-c938-48a3-b134-3a01c950f3fc

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hConnected : G.Connected) :
    Fintype.card V ≤ G.edgeSet.ncard + 1 := by
  simpa [Set.ncard] using hConnected.card_vert_le_card_edgeSet_add_one