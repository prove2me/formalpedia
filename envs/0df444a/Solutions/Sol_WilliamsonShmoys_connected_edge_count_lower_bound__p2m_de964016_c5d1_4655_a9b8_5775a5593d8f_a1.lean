-- Prove2me | solution 1 for WilliamsonShmoys.connected_edge_count_lower_bound__p2m_de964016_c5d1_4655_a9b8_5775a5593d8f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:27:07.103986+00:00
-- url     : https://prove2.me/submissions/90948f3b-8eeb-4290-8a8b-cbfe6e4f398f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hConn : H.Connected) : Fintype.card V ≤ H.edgeSet.ncard + 1 := by
  simpa using hConn.card_vert_le_card_edgeSet_add_one