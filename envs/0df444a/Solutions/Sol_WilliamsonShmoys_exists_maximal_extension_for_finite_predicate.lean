-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_for_finite_predicate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:42:21.715336+00:00
-- url     : https://prove2.me/submissions/f6d84cf5-2480-4d0b-a71a-789a3dbdb49b

import Mathlib

open SimpleGraph

set_option autoImplicit false

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V → Prop) (K : SimpleGraph V) (hK : P K) : ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧ ∀ M : SimpleGraph V, L ≤ M → P M → M = L := by
  obtain ⟨K, h1, h2, h3⟩ := S181max P K hK
  exact ⟨K, h1, h2, h3⟩
