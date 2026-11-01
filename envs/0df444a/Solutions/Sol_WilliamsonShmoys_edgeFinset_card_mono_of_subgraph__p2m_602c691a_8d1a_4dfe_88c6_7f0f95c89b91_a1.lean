-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_mono_of_subgraph__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:27:22.058037+00:00
-- url     : https://prove2.me/submissions/460542a7-381c-43f5-817d-75528c616859

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    (letI : DecidableRel G.Adj := Classical.decRel _
     letI : DecidableRel H.Adj := Classical.decRel _
     G.edgeFinset.card ≤ H.edgeFinset.card) := by
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : DecidableRel H.Adj := Classical.decRel _
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)