-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_finite_property_9538c7a8_17aa_406f_ad1c_e0bdce92c761
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:35.887858+00:00
-- url     : https://prove2.me/submissions/13bc7dbe-8d98-4da5-9974-de91bebacc6d

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
    (G : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P G)
    (hmono : ∀ ⦃A B : SimpleGraph V⦄, A ≤ B → P B → P A) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
      (∀ K : SimpleGraph V, H ≤ K → P K → K = H) := by
  obtain ⟨K, h1, h2, h3⟩ := S181max P G hP
  exact ⟨K, h1, h2, h3⟩
