-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_property_connected_closure_of_merge_with_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:26:04.058544+00:00
-- url     : https://prove2.me/submissions/de79a86b-2077-44be-9683-07ba9581de4f

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
    (P : SimpleGraph V → Prop)
    (hstep : ∀ K : SimpleGraph V, 3 ≤ Fintype.card V → P K → ¬ K.Connected →
      ∃ L : SimpleGraph V,
        K < L ∧ P L ∧ ∃ u v : V, ¬ K.Reachable u v ∧ L.Adj u v)
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : P G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G < H ∧ H.Connected ∧ P H := by
  obtain ⟨H, h1, h2, h3⟩ := S181max P G hG
  have hconn : H.Connected := by
    by_contra hc
    obtain ⟨L, hlt, hPL, -⟩ := hstep H hV h2 hc
    have := h3 L hlt.le hPL
    subst this
    exact lt_irrefl _ hlt
  refine ⟨H, lt_of_le_of_ne h1 ?_, hconn, h2⟩
  rintro rfl
  exact hDisconnected hconn
