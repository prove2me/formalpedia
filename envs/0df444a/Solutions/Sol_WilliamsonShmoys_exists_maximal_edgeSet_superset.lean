-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_edgeSet_superset
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:41.573356+00:00
-- url     : https://prove2.me/submissions/3ae0d4c9-be28-4362-be9d-f58b41cbb679

import Mathlib

set_option autoImplicit false

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ G H : SimpleGraph V,
      P H → G.edgeSet ⊆ H.edgeSet → P G)
    (K : SimpleGraph V)
    (hK : P K) :
    ∃ H : SimpleGraph V,
      P H ∧
      K.edgeSet ⊆ H.edgeSet ∧
      ∀ L : SimpleGraph V,
        P L → H.edgeSet ⊆ L.edgeSet → L.edgeSet ⊆ H.edgeSet := by
  obtain ⟨H, h1, h2, h3⟩ := S181max P K hK
  exact ⟨H, h2, SimpleGraph.edgeSet_mono h1, fun L hPL hL => by
    rw [h3 L (SimpleGraph.edgeSet_subset_edgeSet.1 hL) hPL]⟩
