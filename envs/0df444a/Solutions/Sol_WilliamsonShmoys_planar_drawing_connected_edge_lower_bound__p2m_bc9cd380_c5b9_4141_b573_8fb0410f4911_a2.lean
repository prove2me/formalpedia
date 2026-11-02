-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_edge_lower_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:18:17.835495+00:00
-- url     : https://prove2.me/submissions/d3998e03-689d-4c0d-b6e6-f993215e38c0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hConn : G.Connected) :
    Fintype.card V ≤ (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 1 := by
  letI : DecidableRel G.Adj := dG
  have h := SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one hConn
  simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] using h