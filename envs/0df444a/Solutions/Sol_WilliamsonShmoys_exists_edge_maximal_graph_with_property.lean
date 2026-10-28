-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_graph_with_property
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:37.413665+00:00
-- url     : https://prove2.me/submissions/fc11d0f4-0e0b-44fa-8983-e39a75fca9a3

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
    (J : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P J) :
    ∃ K : SimpleGraph V,
      J.edgeSet ⊆ K.edgeSet ∧
      P K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        P L →
        L.edgeSet = K.edgeSet := by
  obtain ⟨K, h1, h2, h3⟩ := S181max P J hP
  exact ⟨K, SimpleGraph.edgeSet_mono h1, h2, fun L hL hPL => by
    rw [h3 L (SimpleGraph.edgeSet_subset_edgeSet.1 hL) hPL]⟩
