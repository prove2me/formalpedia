-- Prove2me | solution 1 for SCCThm8.realize_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:57:00.414478+00:00
-- url     : https://prove2.me/submissions/eb7c7f10-2b33-4c37-9439-7ed5d2b41ed8

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
public import Theorems.Thm_SCCThm8_mem_ite_insert

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {α : Type*} [DecidableEq α] (m : α → ℕ) (hm : ∀ i, m i ≤ 3)
    (s : Finset α) :
    ∃ A B C : Finset α, A ⊆ s ∧ B ⊆ s ∧ C ⊆ s ∧
      A.card = (∑ i ∈ s, m i + 2) / 3 ∧ B.card = (∑ i ∈ s, m i + 1) / 3 ∧
      C.card = (∑ i ∈ s, m i) / 3 ∧
      ∀ i ∈ s, (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0) +
        (if i ∈ C then 1 else 0) = m i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, ∅, ∅, by simp⟩
  | insert x s hx ih =>
    obtain ⟨A, B, C, hA, hB, hC, cA, cB, cC, hmul⟩ := ih
    have ht := hm x
    have hxA : x ∉ A := fun h => hx (hA h)
    have hxB : x ∉ B := fun h => hx (hB h)
    have hxC : x ∉ C := fun h => hx (hC h)
    rw [sum_insert hx]
    set N := ∑ i ∈ s, m i
    refine ⟨if (m x + N + 2) / 3 ≠ (N + 2) / 3 then insert x A else A,
      if (m x + N + 1) / 3 ≠ (N + 1) / 3 then insert x B else B,
      if (m x + N) / 3 ≠ N / 3 then insert x C else C, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · split_ifs
      · exact insert_subset_insert _ hA
      · exact hA.trans (subset_insert _ _)
    · split_ifs
      · exact insert_subset_insert _ hB
      · exact hB.trans (subset_insert _ _)
    · split_ifs
      · exact insert_subset_insert _ hC
      · exact hC.trans (subset_insert _ _)
    · split_ifs with h
      · rw [card_insert_of_notMem hxA]; omega
      · omega
    · split_ifs with h
      · rw [card_insert_of_notMem hxB]; omega
      · omega
    · split_ifs with h
      · rw [card_insert_of_notMem hxC]; omega
      · omega
    · intro i hi
      simp only [mem_ite_insert]
      rcases mem_insert.1 hi with rfl | hi
      · simp only [hxA, hxB, hxC, and_true, or_false]
        split_ifs <;> omega
      · have hix : i ≠ x := fun h => hx (h ▸ hi)
        simp only [hix, and_false, false_or]
        exact hmul i hi
end SCCThm8
