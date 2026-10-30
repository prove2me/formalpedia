-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_extension_to_connected__p2m_50dbeb3a_1765_4569_965c_952b7ed019cf_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:30:31.293146+00:00
-- url     : https://prove2.me/submissions/987a2495-0b3e-4793-960b-ba969186e749

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] (H : SimpleGraph V)
    (P : SimpleGraph V → Prop) (hP : P H)
    (hstep : ∀ G : SimpleGraph V, P G → ¬ G.Connected →
      ∃ K : SimpleGraph V, G.edgeSet ⊂ K.edgeSet ∧ P K) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ P K ∧ K.Connected := by
  classical
  let N : Nat := (⊤ : SimpleGraph V).edgeFinset.card
  have edge_bound (G : SimpleGraph V) : G.edgeFinset.card ≤ N := by
    dsimp [N]
    apply Finset.card_le_card
    exact (SimpleGraph.edgeFinset_subset_edgeFinset).2 le_top
  have aux : ∀ n : Nat, ∀ G : SimpleGraph V,
      N - G.edgeFinset.card = n → P G →
      ∃ K : SimpleGraph V, G.edgeSet ⊆ K.edgeSet ∧ P K ∧ K.Connected := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hn hPG
      by_cases hconn : G.Connected
      · exact ⟨G, Set.Subset.rfl, hPG, hconn⟩
      · obtain ⟨K, hstrict, hPK⟩ := hstep G hPG hconn
        have hstrictFin : G.edgeFinset ⊂ K.edgeFinset := by
          change ((G.edgeFinset : Set (Sym2 V)) ⊂
            (K.edgeFinset : Set (Sym2 V)))
          rw [SimpleGraph.coe_edgeFinset, SimpleGraph.coe_edgeFinset]
          exact hstrict
        have hcard : G.edgeFinset.card < K.edgeFinset.card :=
          Finset.card_lt_card hstrictFin
        have hKbound : K.edgeFinset.card ≤ N := edge_bound K
        have hmeasure : N - K.edgeFinset.card < n := by omega
        obtain ⟨L, hKL, hPL, hLconn⟩ :=
          ih (N - K.edgeFinset.card) hmeasure K rfl hPK
        exact ⟨L, hstrict.1.trans hKL, hPL, hLconn⟩
  obtain ⟨K, hHK, hPK, hKconn⟩ := aux (N - H.edgeFinset.card) H rfl hP
  exact ⟨K, hHK, hPK, hKconn⟩