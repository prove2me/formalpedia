-- Prove2me | solution 1 for WilliamsonShmoys.small_simple_graph_edge_count_bound__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:28:51.11335+00:00
-- url     : https://prove2.me/submissions/eaebce0e-931b-49a9-9f52-8fdd31599df5

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (hCard : Fintype.card V < 3) : G.edgeSet.ncard <= Fintype.card V / 2 := by
  classical
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have h := G.card_edgeFinset_le_card_choose_two
  interval_cases hn : Fintype.card V <;> simp_all
