-- Prove2me | solution 1 for QuantumLTF.Majority.intersectionIndex_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T02:56:47.414288+00:00
-- url     : https://prove2.me/submissions/69007adc-f32d-4b54-81b3-27e9104736dc

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
namespace QuantumLTF.Majority

open QAlgorithms

theorem intersectionIndex_fiber_card : ∀ n r : ℕ, r ≤ n → ∀ A : ExactSupports n r, ∀ a : Fin (r+1), (Finset.univ.filter fun S : Qubits n => intersectionIndex A S = a).card = 2^(n-r) * r.choose a := by
  intro n r hr A a
  have key : (Finset.univ.filter fun S : Qubits n => intersectionIndex A S = a).card
      = ((A.1.powersetCard a) ×ˢ (A.1ᶜ.powerset)).card := by
    apply Finset.card_nbij' (fun S => (A.1.filter (fun i => S i = true), A.1ᶜ.filter (fun i => S i = true)))
      (fun XY => fun i => decide (i ∈ XY.1 ∪ XY.2))
    · intro S hS
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hS
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powersetCard,
        Finset.mem_powerset]
      refine ⟨⟨Finset.filter_subset _ _, ?_⟩, Finset.filter_subset _ _⟩
      have := congrArg Fin.val hS
      simpa [intersectionIndex] using this
    · intro XY hXY
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powersetCard,
        Finset.mem_powerset] at hXY
      obtain ⟨⟨h1, h2⟩, h3⟩ := hXY
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      apply Fin.ext
      simp only [intersectionIndex]
      rw [← h2]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_union, decide_eq_true_eq]
      constructor
      · rintro ⟨hi, hi' | hi'⟩
        · exact hi'
        · exact absurd hi (Finset.mem_compl.1 (h3 hi'))
      · intro hi; exact ⟨h1 hi, Or.inl hi⟩
    · intro S _
      funext i
      by_cases hi : i ∈ A.1 <;> simp [hi]
    · intro XY hXY
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powersetCard,
        Finset.mem_powerset] at hXY
      obtain ⟨⟨h1, h2⟩, h3⟩ := hXY
      obtain ⟨X, Y⟩ := XY
      simp only at h1 h2 h3 ⊢
      ext i
      · simp only [Finset.mem_filter, Finset.mem_union, decide_eq_true_eq]
        constructor
        · rintro ⟨hi, hi' | hi'⟩
          · exact hi'
          · exact absurd hi (Finset.mem_compl.1 (h3 hi'))
        · intro hi; exact ⟨h1 hi, Or.inl hi⟩
      · simp only [Finset.mem_filter, Finset.mem_union, decide_eq_true_eq]
        constructor
        · rintro ⟨hi, hi' | hi'⟩
          · exact absurd (h1 hi') (Finset.mem_compl.1 hi)
          · exact hi'
        · intro hi; exact ⟨h3 hi, Or.inr hi⟩
  rw [key, Finset.card_product, Finset.card_powersetCard, Finset.card_powerset,
    Finset.card_compl, A.2, Fintype.card_fin, mul_comm]

end QuantumLTF.Majority

open QAlgorithms in
theorem solution : ∀ n r : ℕ, r ≤ n → ∀ A : QuantumLTF.Majority.ExactSupports n r, ∀ a : Fin (r+1), (Finset.univ.filter fun S : Qubits n => QuantumLTF.Majority.intersectionIndex A S = a).card = 2^(n-r) * r.choose a :=
  QuantumLTF.Majority.intersectionIndex_fiber_card
