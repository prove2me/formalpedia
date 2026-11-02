-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_graph_has_unreachable_pair__p2m_a01887ab_b605_44b6_af24_b6696d8b1f6b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:53:55.019326+00:00
-- url     : https://prove2.me/submissions/c1f11e81-995e-4fe2-8496-d78276be11e6

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdis : ¬ K.Connected) :
    ∃ a b : V, a ≠ b ∧ ¬ K.Adj a b ∧ ¬ K.Reachable a b := by
  haveI : Nonempty V := by
    apply Fintype.card_pos_iff.mp
    omega
  rw [K.connected_iff_exists_forall_reachable] at hdis
  obtain ⟨a⟩ := ‹Nonempty V›
  have hb : ∃ b, ¬ K.Reachable a b := by
    by_contra hn
    push Not at hn
    exact hdis ⟨a, hn⟩
  obtain ⟨b, hab⟩ := hb
  have hne : a ≠ b := by
    intro heq
    subst b
    exact hab SimpleGraph.Reachable.rfl
  have hnadj : ¬ K.Adj a b := by
    intro hadj
    exact hab hadj.reachable
  exact ⟨a, b, hne, hnadj, hab⟩
