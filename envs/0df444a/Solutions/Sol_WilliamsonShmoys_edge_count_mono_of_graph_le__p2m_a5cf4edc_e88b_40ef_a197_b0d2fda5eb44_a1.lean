-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_mono_of_graph_le__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:04:37.243727+00:00
-- url     : https://prove2.me/submissions/d8cdba50-b81e-4317-a7aa-f3069e2635b2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V}
    (h : G ≤ H) : G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono h)