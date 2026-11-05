-- Prove2me | solution 1 for WilliamsonShmoys.finite_block_edge_bound_aggregation__p2m_a70877ba_ee67_4eb5_a950_6d5f423393ca_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:23:36.38291+00:00
-- url     : https://prove2.me/submissions/fe80faf8-219d-4f11-a286-e968740d9405

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {α : Type} (C : Finset α) (n e : α → Nat)
    (hn : ∀ a ∈ C, 0 < n a)
    (he1 : ∀ a ∈ C, n a = 1 → e a = 0)
    (he2 : ∀ a ∈ C, n a = 2 → e a ≤ 1)
    (hebig : ∀ a ∈ C, 3 ≤ n a → e a + 6 ≤ 3 * n a)
    (htotal : 3 ≤ ∑ a ∈ C, n a) :
    (∑ a ∈ C, e a) + 6 ≤ 3 * (∑ a ∈ C, n a) := by
  have hlocal : ∀ a ∈ C, e a + 3 ≤ 3 * n a := by
    intro a ha
    have hna : 0 < n a := hn a ha
    by_cases h1 : n a = 1
    · have he := he1 a ha h1
      omega
    · by_cases h2 : n a = 2
      · have he := he2 a ha h2
        omega
      · have h3 : 3 ≤ n a := by omega
        have he := hebig a ha h3
        omega
  have hsum : (∑ a ∈ C, (e a + 3)) ≤ ∑ a ∈ C, (3 * n a) :=
    Finset.sum_le_sum (fun a ha => hlocal a ha)
  have hconst : (∑ a ∈ C, (3 : Nat)) = 3 * C.card := by
    simp [Nat.mul_comm]
  have hmain : (∑ a ∈ C, e a) + 3 * C.card ≤ 3 * (∑ a ∈ C, n a) := by
    calc
      (∑ a ∈ C, e a) + 3 * C.card
          = (∑ a ∈ C, e a) + (∑ a ∈ C, (3 : Nat)) := by rw [hconst]
      _ = ∑ a ∈ C, (e a + 3) := by rw [Finset.sum_add_distrib]
      _ ≤ ∑ a ∈ C, (3 * n a) := hsum
      _ = 3 * (∑ a ∈ C, n a) := by rw [Finset.mul_sum]
  by_cases hc : 2 ≤ C.card
  · have h6 : 6 ≤ 3 * C.card := by omega
    omega
  · have hcard_pos : 0 < C.card := by
      by_contra h0
      have hc0 : C.card = 0 := by omega
      have hCe : C = ∅ := Finset.card_eq_zero.mp hc0
      have hz : (∑ a ∈ C, n a) = 0 := by simp [hCe]
      omega
    have hc1 : C.card = 1 := by omega
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
    have hna : 3 ≤ n a := by simpa using htotal
    have he := hebig a (by simp) hna
    simpa using he
