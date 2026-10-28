-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_simpleGraph_of_downward_closed_property
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:44.131116+00:00
-- url     : https://prove2.me/submissions/91ffe1ab-faf7-45be-8df7-00e21e406c0c

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
    {V : Type} [Fintype V] [DecidableEq V]
    (Good : SimpleGraph V → Prop)
    (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → Good B → Good A)
    (G : SimpleGraph V)
    (hG : Good G) :
    ∃ P : SimpleGraph V,
      G ≤ P ∧ Good P ∧
        ∀ Q : SimpleGraph V, P ≤ Q → Good Q → Q ≤ P := by
  obtain ⟨K, h1, h2, h3⟩ := S181max Good G hG
  exact ⟨K, h1, h2, fun L hL hQ => (h3 L hL hQ).le⟩
