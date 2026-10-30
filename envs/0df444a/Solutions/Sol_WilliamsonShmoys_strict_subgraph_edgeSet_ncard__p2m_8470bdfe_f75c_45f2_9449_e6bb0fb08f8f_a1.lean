-- Prove2me | solution 1 for WilliamsonShmoys.strict_subgraph_edgeSet_ncard__p2m_8470bdfe_f75c_45f2_9449_e6bb0fb08f8f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:44:43.81266+00:00
-- url     : https://prove2.me/submissions/352b7df7-a252-47ab-99a0-32f12cc7bc50

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G K : SimpleGraph V)
    (hsub : G ≤ K)
    (hne : G ≠ K) :
    G.edgeSet.ncard < K.edgeSet.ncard := by
  have hex : ∃ a b, K.Adj a b ∧ ¬ G.Adj a b := by
    by_contra h
    apply hne
    ext a b
    constructor
    · intro hGab
      exact hsub hGab
    · intro hKab
      by_contra hGab
      exact h ⟨a, b, hKab, hGab⟩
  have hss : G.edgeSet ⊂ K.edgeSet := by
    refine ⟨SimpleGraph.edgeSet_mono hsub, ?_⟩
    intro hKG
    obtain ⟨a, b, hKab, hGab⟩ := hex
    have hmem : Sym2.mk a b ∈ K.edgeSet := by
      simpa using hKab
    have hmemG : Sym2.mk a b ∈ G.edgeSet := hKG hmem
    exact hGab (by simpa using hmemG)
  exact Set.ncard_lt_ncard hss (Set.toFinite K.edgeSet)