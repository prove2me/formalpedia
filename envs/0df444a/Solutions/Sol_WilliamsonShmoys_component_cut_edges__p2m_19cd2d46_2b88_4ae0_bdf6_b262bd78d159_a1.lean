-- Prove2me | solution 1 for WilliamsonShmoys.component_cut_edges__p2m_19cd2d46_2b88_4ae0_bdf6_b262bd78d159_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:43:51.8233+00:00
-- url     : https://prove2.me/submissions/bd6a63bb-2dbe-4de1-9d8c-d1c7994e693b

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V)
    (hdisj : ¬ G.Reachable u v) :
    ∃ S : Set V, ∃ A B : SimpleGraph V,
      u ∈ S ∧ v ∉ S ∧
      (∀ a b, G.Adj a b ↔ A.Adj a b ∨ B.Adj a b) ∧
      (∀ a b, A.Adj a b → a ∈ S ∧ b ∈ S) ∧
      (∀ a b, B.Adj a b → a ∉ S ∧ b ∉ S) := by
  let S : Set V := {x | G.Reachable u x}
  let A : SimpleGraph V := {
    Adj := fun a b => G.Adj a b ∧ a ∈ S ∧ b ∈ S
    symm := ⟨by
      intro a b hab
      exact ⟨G.adj_symm hab.1, hab.2.2, hab.2.1⟩⟩
  }
  let B : SimpleGraph V := {
    Adj := fun a b => G.Adj a b ∧ a ∉ S ∧ b ∉ S
    symm := ⟨by
      intro a b hab
      exact ⟨G.adj_symm hab.1, hab.2.2, hab.2.1⟩⟩
  }
  refine ⟨S, A, B, ?_, ?_, ?_, ?_, ?_⟩
  · change G.Reachable u u
    exact SimpleGraph.Reachable.rfl
  · exact hdisj
  · intro a b
    change G.Adj a b ↔
      (G.Adj a b ∧ a ∈ S ∧ b ∈ S) ∨ (G.Adj a b ∧ a ∉ S ∧ b ∉ S)
    constructor
    · intro hab
      have hadj : G.Reachable a b := hab.reachable
      by_cases ha : a ∈ S
      · have hb : b ∈ S := by
          change G.Reachable u b
          exact SimpleGraph.Reachable.trans ha hadj
        exact Or.inl ⟨hab, ha, hb⟩
      · have hb : b ∉ S := by
          intro hb
          apply ha
          change G.Reachable u a
          exact SimpleGraph.Reachable.trans hb hadj.symm
        exact Or.inr ⟨hab, ha, hb⟩
    · intro hab
      rcases hab with hA | hB
      · exact hA.1
      · exact hB.1
  · intro a b hab
    exact ⟨hab.2.1, hab.2.2⟩
  · intro a b hab
    exact ⟨hab.2.1, hab.2.2⟩
