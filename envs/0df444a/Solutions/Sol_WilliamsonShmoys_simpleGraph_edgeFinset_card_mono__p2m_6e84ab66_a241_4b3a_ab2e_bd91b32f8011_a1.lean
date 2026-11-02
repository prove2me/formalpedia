-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_edgeFinset_card_mono__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:30:00.81733+00:00
-- url     : https://prove2.me/submissions/caa94e4d-cdc2-49af-90b8-27b035fe5af0

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G ≤ H) :
    G.edgeFinset.card ≤ H.edgeFinset.card := by
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono h)