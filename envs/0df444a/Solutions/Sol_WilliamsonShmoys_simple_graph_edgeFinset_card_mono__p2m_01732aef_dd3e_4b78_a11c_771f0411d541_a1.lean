-- Prove2me | solution 1 for WilliamsonShmoys.simple_graph_edgeFinset_card_mono__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:07:54.309369+00:00
-- url     : https://prove2.me/submissions/7852235c-d260-4e64-8555-b3ee76d8e9ea

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V) (hKH : K ≤ H) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj; K.edgeFinset.card) ≤
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj; H.edgeFinset.card) := by
  classical
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hKH)