-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_maximal_extension__p2m_bdc3b847_9c7d_4952_b797_9d04867ba893_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:25:02.677776+00:00
-- url     : https://prove2.me/submissions/c15cfa18-687c-4639-b135-d4a2f7cdae1b

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (Q : SimpleGraph V → Prop)
    (hmono : ∀ ⦃G H : SimpleGraph V⦄, H.edgeSet ⊆ G.edgeSet → Q G → Q H)
    (M : SimpleGraph V)
    (hM : Q M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      Q N ∧
      ∀ P : SimpleGraph V,
        N.edgeSet ⊆ P.edgeSet →
        Q P →
        P.edgeSet = N.edgeSet := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => M ≤ G ∧ Q G
  have hMmem : M ∈ S := by
    simp [S, hM]
  obtain ⟨N, hNmem, hNmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) ⟨M, hMmem⟩
  have hN : M ≤ N ∧ Q N := by
    simpa [S] using hNmem
  refine ⟨N, SimpleGraph.edgeSet_subset_edgeSet.mpr hN.1, hN.2, ?_⟩
  intro P hNP hQP
  have hNPle : N ≤ P := SimpleGraph.edgeSet_subset_edgeSet.mp hNP
  have hPmem : P ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hN.1.trans hNPle, hQP⟩
  have hcard : P.edgeFinset.card ≤ N.edgeFinset.card := hNmax P hPmem
  have hEq : N = P := by
    by_contra hne
    have hsub : N.edgeFinset ⊆ P.edgeFinset :=
      SimpleGraph.edgeFinset_subset_edgeFinset.mpr hNPle
    have hss : N.edgeFinset ⊂ P.edgeFinset := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨hsub, ?_⟩
      intro heq
      exact hne (SimpleGraph.edgeFinset_inj.mp heq)
    exact (not_le_of_gt (Finset.card_lt_card hss)) hcard
  simpa [hEq]