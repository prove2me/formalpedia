-- Prove2me | solution 1 for WilliamsonShmoys.edge_card_mono__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:53:16.811793+00:00
-- url     : https://prove2.me/submissions/77f4993f-37b0-4792-9c79-001cd5c65938

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (G K : SimpleGraph V) (hGK : G ≤ K) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : DecidableRel K.Adj := Classical.decRel K.Adj
     G.edgeFinset.card ≤ K.edgeFinset.card) := by
  classical
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hGK)