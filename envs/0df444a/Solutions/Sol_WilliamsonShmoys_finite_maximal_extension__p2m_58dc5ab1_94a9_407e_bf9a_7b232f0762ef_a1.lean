-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension__p2m_58dc5ab1_94a9_407e_bf9a_7b232f0762ef_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:24:30.291093+00:00
-- url     : https://prove2.me/submissions/b0903024-0c32-4c49-8d5d-1675e0db335b

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (P : SimpleGraph V → Prop) (hW : P W) :
    letI : DecidableRel W.Adj := Classical.decRel W.Adj
    ∃ H : SimpleGraph V, P H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       W.edgeFinset ⊆ H.edgeFinset) ∧
      ∀ K : SimpleGraph V, P K →
        (letI : DecidableRel H.Adj := Classical.decRel H.Adj
         letI : DecidableRel K.Adj := Classical.decRel K.Adj
         H.edgeFinset ⊆ K.edgeFinset → K.edgeFinset ⊆ H.edgeFinset) := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter fun G => P G ∧ W ≤ G
  have hWmem : W ∈ S := by
    simp [S, hW]
  obtain ⟨H, hHmem, hmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) ⟨W, hWmem⟩
  have hH : P H ∧ W ≤ H := (Finset.mem_filter.mp hHmem).2
  refine ⟨H, hH.1, ?_, ?_⟩
  · simpa only [SimpleGraph.edgeFinset_subset_edgeFinset] using hH.2
  · intro K hK hHK
    have hKmem : K ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ K, hK, ?_⟩
      exact le_trans hH.2 (SimpleGraph.edgeFinset_subset_edgeFinset.mp hHK)
    by_contra hKH
    have hproper : H.edgeFinset ⊂ K.edgeFinset :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hHK, by
        intro heq
        apply hKH
        simpa [heq]⟩
    have hcard : H.edgeFinset.card < K.edgeFinset.card := Finset.card_lt_card hproper
    have hmaxK := hmax K hKmem
    omega