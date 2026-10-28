-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_finite_property_f877e9d9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:44:26.020953+00:00
-- url     : https://prove2.me/submissions/25dcde21-df7a-4c14-968f-16d9e3eda4b5

import Mathlib

open SimpleGraph

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V)
    (hK : P K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      P H ∧
      (∀ J : SimpleGraph V, H ≤ J → P J → J = H) ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let Q : SimpleGraph V → Prop := fun G => K ≤ G ∧ P G
  have hQ : ∃ G : SimpleGraph V, Q G := ⟨K, le_rfl, hK⟩
  obtain ⟨H, _, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists Q).2 hQ
  have hQH : Q H := hExt.1
  refine ⟨H, hQH.1, hQH.2, ?_, ?_⟩
  · intro J hHJ hPJ
    have hQJ : Q J := ⟨hQH.1.trans hHJ, hPJ⟩
    have hEdgeEq : H.edgeFinset = J.edgeFinset :=
      Finset.eq_of_subset_of_card_le
        (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hHJ)
        (hExt.2 hQJ)
    exact (SimpleGraph.edgeFinset_inj.mp hEdgeEq).symm
  · have hsub : K.edgeFinset ⊆ H.edgeFinset :=
      SimpleGraph.edgeFinset_subset_edgeFinset.mpr hQH.1
    have hcard : K.edgeFinset.card ≤ H.edgeFinset.card :=
      Finset.card_le_card hsub
    have hnk : K.edgeSet.ncard = K.edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    have hnh : H.edgeSet.ncard = H.edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    rw [hnk, hnh]
    exact hcard