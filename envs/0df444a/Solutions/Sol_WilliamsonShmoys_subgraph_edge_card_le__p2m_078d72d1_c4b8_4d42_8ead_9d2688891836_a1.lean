-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_edge_card_le__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:00:42.310299+00:00
-- url     : https://prove2.me/submissions/78327fe4-8bcf-406a-83aa-cbe5e2ecd821

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G F : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel F.Adj]
    (hGF : G <= F) : G.edgeFinset.card <= F.edgeFinset.card := by
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hGF)