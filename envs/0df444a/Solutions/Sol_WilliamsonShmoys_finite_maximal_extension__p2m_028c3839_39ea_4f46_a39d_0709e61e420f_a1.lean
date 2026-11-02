-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension__p2m_028c3839_39ea_4f46_a39d_0709e61e420f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:08:25.941206+00:00
-- url     : https://prove2.me/submissions/6743b4e0-b7a7-4a69-ae83-9a39c1dab57b

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop) (M : SimpleGraph V) (hM : P M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ P N ∧
      ∀ K : SimpleGraph V, N ≤ K → P K → K = N := by
  classical
  letI : DecidableEq V := Classical.decEq V
  letI : DecidablePred P := Classical.decPred P
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => M ≤ G ∧ P G
  have hS : S.Nonempty := by
    exact ⟨M, by simp [S, hM]⟩
  let A : Finset ℕ := S.image fun G => G.edgeFinset.card
  have hA : A.Nonempty := by
    rcases hS with ⟨G, hG⟩
    exact ⟨G.edgeFinset.card, Finset.mem_image.mpr ⟨G, hG, rfl⟩⟩
  obtain ⟨N, hNS, hNcard⟩ := Finset.mem_image.mp (Finset.max'_mem A hA)
  have hMN : M ≤ N := (Finset.mem_filter.mp hNS).2.1
  have hPN : P N := (Finset.mem_filter.mp hNS).2.2
  refine ⟨N, hMN, hPN, ?_⟩
  intro K hNK hPK
  by_contra hKN
  have hne : N ≠ K := fun h => hKN h.symm
  have hlt : N < K := lt_of_le_of_ne hNK hne
  have hEdges : N.edgeFinset ⊂ K.edgeFinset :=
    SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt
  have hCardLt : N.edgeFinset.card < K.edgeFinset.card := Finset.card_lt_card hEdges
  have hKS : K ∈ S := by simp [S, hMN.trans hNK, hPK]
  have hKmax : K.edgeFinset.card ≤ A.max' hA :=
    Finset.le_max' A (K.edgeFinset.card)
      (Finset.mem_image.mpr ⟨K, hKS, rfl⟩)
  omega