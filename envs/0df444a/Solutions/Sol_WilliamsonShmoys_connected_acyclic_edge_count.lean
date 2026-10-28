-- Prove2me | solution 1 for WilliamsonShmoys.connected_acyclic_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:32:07.65154+00:00
-- url     : https://prove2.me/submissions/740e706b-eb9b-4cbe-8ddd-f4153a9ba642

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hAcyclic : G.IsAcyclic) :
    G.edgeSet.ncard + 1 = Fintype.card V := by
  classical
  have hTree : G.IsTree := ⟨hConnected, hAcyclic⟩
  simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using
    hTree.card_edgeFinset