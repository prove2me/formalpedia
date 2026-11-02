-- Prove2me | solution 1 for WilliamsonShmoys.graph_edge_completion__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T20:00:11.022605+00:00
-- url     : https://prove2.me/submissions/0f214333-2e2b-4506-a294-cecff68571c9

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 0

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (m : Nat) :
    letI : (G : SimpleGraph V) → DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    K.edgeFinset.card ≤ m →
    m ≤ Fintype.card V * (Fintype.card V - 1) / 2 →
    ∃ H : SimpleGraph V, K ≤ H ∧ H.edgeFinset.card = m := by
  intro hKm hm
  classical
  let T : SimpleGraph V := ⊤
  have htop : K.edgeFinset ⊆ T.edgeFinset := by
    exact SimpleGraph.edgeFinset_mono (show K ≤ T from le_top)
  have hTopCard : m ≤ T.edgeFinset.card := by
    calc
      m ≤ (Fintype.card V).choose 2 := by
        rw [Nat.choose_two_right]
        exact hm
      _ = T.edgeFinset.card := by
        dsimp [T]
        exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two.symm
  obtain ⟨u, hKu, huTop, hucard⟩ :=
    Finset.exists_subsuperset_card_eq htop hKm hTopCard
  let removed : Finset (Sym2 V) := T.edgeFinset \ u
  let H : SimpleGraph V := T.deleteEdges (removed : Set (Sym2 V))
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hExact : H.edgeFinset = u := by
    change (T.deleteEdges (removed : Set (Sym2 V))).edgeFinset = u
    rw [SimpleGraph.edgeFinset_deleteEdges]
    ext e
    simp only [removed, Finset.mem_sdiff]
    constructor
    · rintro ⟨heTop, hnot⟩
      by_contra heu
      exact hnot ⟨heTop, heu⟩
    · intro heu
      exact ⟨huTop heu, fun h => h.2 heu⟩
  refine ⟨H, ?_, ?_⟩
  · apply (SimpleGraph.edgeFinset_subset_edgeFinset).mp
    rw [hExact]
    exact hKu
  · exact (congrArg Finset.card hExact).trans hucard
