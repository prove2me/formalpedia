-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_predicate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:33:53.920404+00:00
-- url     : https://prove2.me/submissions/a86b22c3-0528-43e7-8a45-e20a615d1dd4

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (M : SimpleGraph V) (hP : P M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ P N ∧
      ∀ K : SimpleGraph V, N ≤ K → P K → K ≤ N := by
  classical
  let feasible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => M ≤ G ∧ P G
  have hfeasible : feasible.Nonempty := by
    refine ⟨M, ?_⟩
    simp [feasible, hP]
  obtain ⟨N, hNfeasible, hNmax⟩ :=
    feasible.exists_max_image (fun G => G.edgeFinset.card) hfeasible
  have hNprops : M ≤ N ∧ P N := (Finset.mem_filter.mp hNfeasible).2
  refine ⟨N, hNprops.1, hNprops.2, ?_⟩
  intro K hNK hPK
  have hKfeasible : K ∈ feasible := by
    simp only [feasible, Finset.mem_filter, Finset.mem_univ]
    constructor
    · trivial
    · exact ⟨hNprops.1.trans hNK, hPK⟩
  have hcard : K.edgeFinset.card ≤ N.edgeFinset.card := hNmax K hKfeasible
  have hsub : N.edgeFinset ⊆ K.edgeFinset :=
    (SimpleGraph.edgeFinset_subset_edgeFinset).2 hNK
  have heq : N.edgeFinset = K.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard
  exact (SimpleGraph.edgeFinset_subset_edgeFinset).1 (by simpa [heq])