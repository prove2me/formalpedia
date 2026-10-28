-- Prove2me | solution 1 for WilliamsonShmoys.exists_connected_supergraph_of_finite_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:35.138087+00:00
-- url     : https://prove2.me/submissions/5a89f50d-b13b-48d6-8379-9c19af4c1e18

import Mathlib

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P H)
    (hstep : ∀ G : SimpleGraph V,
      H.edgeSet ⊆ G.edgeSet →
      P G →
      ¬ G.Connected →
      ∃ K : SimpleGraph V, G.edgeSet ⊂ K.edgeSet ∧ P K) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧ K.Connected ∧ P K := by
  obtain ⟨K, h1, h2, h3⟩ := S181max (fun G => H.edgeSet ⊆ G.edgeSet ∧ P G) H ⟨subset_rfl, hP⟩
  refine ⟨K, h2.1, ?_, h2.2⟩
  by_contra hc
  obtain ⟨K', hss, hPK'⟩ := hstep K h2.1 h2.2 hc
  have hle : K ≤ K' := SimpleGraph.edgeSet_subset_edgeSet.1 hss.subset
  have := h3 K' hle ⟨h2.1.trans hss.subset, hPK'⟩
  subst this
  exact hss.ne rfl
