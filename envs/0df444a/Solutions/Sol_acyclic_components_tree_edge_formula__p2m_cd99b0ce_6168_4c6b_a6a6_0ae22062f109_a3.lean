-- Prove2me | solution 1 for acyclic_components_tree_edge_formula__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:28:27.771914+00:00
-- url     : https://prove2.me/submissions/e7bf42b2-5064-40a5-a279-39830fe4571a

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Set.Card

open SimpleGraph

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (C : G.ConnectedComponent) :
    C.toSimpleGraph.edgeSet.ncard + 1 = Nat.card (C : Set V) := by
  classical
  have htree : C.toSimpleGraph.IsTree := hG.isTree_connectedComponent C
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  simpa using htree.card_edgeFinset