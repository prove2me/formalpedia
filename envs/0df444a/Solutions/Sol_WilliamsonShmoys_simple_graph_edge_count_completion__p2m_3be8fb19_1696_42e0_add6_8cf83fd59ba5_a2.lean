-- Prove2me | solution 1 for WilliamsonShmoys.simple_graph_edge_count_completion__p2m_3be8fb19_1696_42e0_add6_8cf83fd59ba5_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:00:02.187434+00:00
-- url     : https://prove2.me/submissions/0293312e-999f-4ad0-9414-d8ec4ce6c917

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (m : Nat)
    (hG : letI : DecidableRel G.Adj := Classical.decRel G.Adj
      G.edgeFinset.card ≤ m)
    (hcap : m ≤ Nat.choose (Fintype.card V) 2) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       H.edgeFinset.card = m) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI : DecidableEq V := Classical.decEq V
  have hsub : G.edgeFinset ⊆ (⊤ : SimpleGraph V).edgeFinset :=
    SimpleGraph.edgeFinset_mono le_top
  have htop : m ≤ (⊤ : SimpleGraph V).edgeFinset.card := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    exact hcap
  obtain ⟨s, hGs, hsTop, hscard⟩ :=
    Finset.exists_subsuperset_card_eq hsub hG htop
  let H : SimpleGraph V := SimpleGraph.fromEdgeSet (s : Set (Sym2 V))
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  letI : Fintype H.edgeSet := H.fintypeEdgeSet
  have hnotdiag : ∀ e ∈ s, e ∉ Sym2.diagSet := by
    intro e hes
    have heTop : e ∈ (⊤ : SimpleGraph V).edgeFinset := hsTop hes
    simpa [SimpleGraph.edgeFinset_top] using heTop
  have hHE : H.edgeSet = (s : Set (Sym2 V)) := by
    dsimp [H]
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_diff]
    constructor
    · intro he
      exact he.1
    · intro he
      exact ⟨he, hnotdiag e he⟩
  have hGH : G ≤ H := by
    change G ≤ SimpleGraph.fromEdgeSet (s : Set (Sym2 V))
    rw [SimpleGraph.le_fromEdgeSet_iff]
    intro e he
    exact hGs (by simpa using he)
  have hcount : Fintype.card H.edgeSet = s.card := by
    calc
      Fintype.card H.edgeSet = Fintype.card (↑s : Set (Sym2 V)) :=
        Fintype.card_congr (Equiv.setCongr hHE)
      _ = s.card := by simp
  have hcard : H.edgeFinset.card = m := by
    calc
      H.edgeFinset.card = Fintype.card H.edgeSet := SimpleGraph.edgeFinset_card
      _ = s.card := hcount
      _ = m := hscard
  exact ⟨H, hGH, hcard⟩
