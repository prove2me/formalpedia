-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_5b94020c_9ee6_4950_8133_0664742e8f38_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:18:48.4222+00:00
-- url     : https://prove2.me/submissions/fd60731e-4df2-4dce-8381-92c5b4fdd02c

import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeSet_ncard_le

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planarDrawingOn_edgeSet_ncard_le G hV hG
