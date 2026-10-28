-- Prove2me | solution 1 for WilliamsonShmoys.finite_edge_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:18:06.512994+00:00
-- url     : https://prove2.me/submissions/b9b6de1a-c064-4812-95d1-1102481c0a32

import Mathlib
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G.edgeSet ⊆ H.edgeSet → P H → P G)
    (H : SimpleGraph V) (hH : P H) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ P K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → P L → L = K := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => H ≤ X0 ∧ P X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hH⟩⟩
  obtain ⟨hPQ, hQ⟩ : H ≤ Q ∧ P Q := (Finset.mem_filter.mp hQm).2
  have key : ∀ R : SimpleGraph V, Q ≤ R → P R → R = Q := by
    intro R hQR hR
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  exact ⟨Q, SimpleGraph.edgeSet_subset_edgeSet.mpr hPQ, hQ,
    fun L h1 h2 => key L (SimpleGraph.edgeSet_subset_edgeSet.mp h1) h2⟩
