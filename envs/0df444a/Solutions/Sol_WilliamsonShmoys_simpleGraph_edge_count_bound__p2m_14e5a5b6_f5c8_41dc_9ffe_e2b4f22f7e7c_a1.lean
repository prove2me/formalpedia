-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_edge_count_bound__p2m_14e5a5b6_f5c8_41dc_9ffe_e2b4f22f7e7c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:06:57.019544+00:00
-- url     : https://prove2.me/submissions/0a9b9b72-1b5a-4ecd-966b-cf3d1dacd2b7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) :
    G.edgeSet.ncard ≤ Nat.choose (Fintype.card V) 2 := by
  classical
  have hfin : G.edgeSet.Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hfin]
  simpa [SimpleGraph.edgeFinset] using G.card_edgeFinset_le_card_choose_two