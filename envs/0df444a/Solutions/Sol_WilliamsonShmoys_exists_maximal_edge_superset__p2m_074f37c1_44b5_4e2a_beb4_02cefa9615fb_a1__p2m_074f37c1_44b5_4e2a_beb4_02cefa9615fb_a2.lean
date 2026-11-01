-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_edge_superset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:33:49.713055+00:00
-- url     : https://prove2.me/submissions/040ea264-afcb-414d-8bbc-9f7a76c20756

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ K : SimpleGraph V,
      H.edgeFinset ⊆ K.edgeFinset ∧
      P K ∧
      ∀ G : SimpleGraph V, K.edgeFinset ⊆ G.edgeFinset → P G → G = K := by
  classical
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H.edgeFinset ⊆ G.edgeFinset ∧ P G
  have hcandidates : candidates.Nonempty := by
    refine ⟨H, ?_⟩
    simp [candidates, hP]
  obtain ⟨K, hK, hmax⟩ :=
    Finset.exists_max_image candidates (fun G => G.edgeFinset.card) hcandidates
  have hKprops : H.edgeFinset ⊆ K.edgeFinset ∧ P K := by
    simpa [candidates] using (Finset.mem_filter.mp hK).2
  refine ⟨K, hKprops.1, hKprops.2, ?_⟩
  intro G hKG hPG
  by_contra hne
  have hneEdges : K.edgeFinset ≠ G.edgeFinset := by
    intro hEdges
    exact hne ((SimpleGraph.edgeFinset_inj).mp hEdges).symm
  have hStrict : K.edgeFinset ⊂ G.edgeFinset := by
    rw [ssubset_iff_subset_ne]
    exact ⟨hKG, hneEdges⟩
  have hCard : K.edgeFinset.card < G.edgeFinset.card := Finset.card_lt_card hStrict
  have hGmem : G ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hKprops.1.trans hKG, hPG⟩
  exact (Nat.not_lt_of_ge (hmax G hGmem)) hCard