-- Prove2me | solution 1 for WilliamsonShmoys.small_induced_simple_graph_edge_bound__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:29:18.695891+00:00
-- url     : https://prove2.me/submissions/b74af841-d206-480d-bfca-ca9c3f821427

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (W : Finset V) (hW : W.card < 3) :
    (M.induce (W : Set V)).edgeSet.ncard ≤ W.card - 1 := by
  classical
  let G : SimpleGraph (↥W) := M.induce (W : Set V)
  have hcard : Fintype.card (↥W) = W.card := by
    simp
  have hedge := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G)
  have hncard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  calc
    G.edgeSet.ncard = G.edgeFinset.card := hncard
    _ ≤ (Fintype.card (↥W)).choose 2 := hedge
    _ ≤ W.card - 1 := by
      rw [hcard]
      interval_cases n : W.card <;> norm_num at hW ⊢