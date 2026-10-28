-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_finite_graph_property
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:48.229687+00:00
-- url     : https://prove2.me/submissions/9d85a964-ac69-475e-9baf-c5c018d7d0c2

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
    (hdown : ∀ A B : SimpleGraph V, A ≤ B → P B → P A)
    (G : SimpleGraph V)
    (hG : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      P H ∧
      ∀ H' : SimpleGraph V, H < H' → ¬ P H' := by
  obtain ⟨K, h1, h2, h3⟩ := S181max P G hG
  exact ⟨K, h1, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono h1) (Set.toFinite _), h2,
    fun H' hlt hP' => hlt.ne (h3 H' hlt.le hP').symm⟩
