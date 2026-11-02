-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_graph_property__p2m_ce5da3a5_6829_4f27_a8ae_e3e80a750393_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:08:31.433959+00:00
-- url     : https://prove2.me/submissions/aafbe438-40be-4212-b284-6f8fa49e71d5

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Preorder.Finite
set_option autoImplicit false

open SimpleGraph

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (Q : SimpleGraph V → Prop) (hQ : Q L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ Q M ∧
      ∀ N : SimpleGraph V, M ≤ N → Q N → N = M := by
  classical
  let S : Set (SimpleGraph V) := {M | L ≤ M ∧ Q M}
  have hS : S.Finite := by
    exact Set.toFinite S
  have hSne : S.Nonempty := ⟨L, le_rfl, hQ⟩
  obtain ⟨M, hM, hMax⟩ := hS.exists_maximal hSne
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro N hMN hQN
  have hN : N ∈ S := ⟨hM.1.trans hMN, hQN⟩
  have hNM : N ≤ M := hMax hN hMN
  exact le_antisymm hNM hMN