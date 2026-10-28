-- Prove2me | solution 1 for WilliamsonShmoys.connected_graph_edge_count_lower_bound__p2m_2aa9d4d8_ca19_4a3e_94b2_47d01f3eb35e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:46:41.120507+00:00
-- url     : https://prove2.me/submissions/3d6bd028-006f-4333-ba8f-0322b5264636

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hG : G.Connected) :
    Fintype.card V ≤ G.edgeSet.ncard + 1 := by
  simpa only [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
    SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one (G := G) hG