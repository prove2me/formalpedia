-- Prove2me | solution 1 for QuantumLTF.Majority.boolean_character_mul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:06:00.9532+00:00
-- url     : https://prove2.me/submissions/f078e18d-c1df-40fb-a7d9-0ab290d672cd

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
namespace QuantumLTF.Majority

open QAlgorithms
open scoped symmDiff

lemma qltf_neg_one_pow_symmDiff {α : Type*} [DecidableEq α] (A B : Finset α) :
    (-1 : ℤ) ^ A.card * (-1 : ℤ) ^ B.card = (-1 : ℤ) ^ (A ∆ B).card := by
  have h1 : A ∆ B = (A \ B) ∪ (B \ A) := rfl
  have hd : Disjoint (A \ B) (B \ A) := disjoint_sdiff_sdiff
  have hA : (A \ B).card + (A ∩ B).card = A.card := Finset.card_sdiff_add_card_inter A B
  have hB : (B \ A).card + (A ∩ B).card = B.card := by
    rw [Finset.inter_comm]; exact Finset.card_sdiff_add_card_inter B A
  rw [h1, Finset.card_union_of_disjoint hd, ← hA, ← hB, ← pow_add]
  have : (A \ B).card + (A ∩ B).card + ((B \ A).card + (A ∩ B).card) =
      ((A \ B).card + (B \ A).card) + 2 * (A ∩ B).card := by ring
  rw [this, pow_add, pow_mul]
  simp

theorem boolean_character_mul : ∀ k : ℕ, ∀ T U : Finset (Fin k), ∀ S : Qubits k, (-1 : ℤ) ^ ((T.filter fun i => S i).card) * (-1 : ℤ) ^ ((U.filter fun i => S i).card) = (-1 : ℤ) ^ (((T ∆ U).filter fun i => S i).card) := by
  intro k T U S
  rw [qltf_neg_one_pow_symmDiff]
  congr 2
  ext i
  simp only [Finset.mem_symmDiff, Finset.mem_filter]
  tauto

end QuantumLTF.Majority

open QAlgorithms in
open scoped symmDiff in
theorem solution : ∀ k : ℕ, ∀ T U : Finset (Fin k), ∀ S : Qubits k, (-1 : ℤ) ^ ((T.filter fun i => S i).card) * (-1 : ℤ) ^ ((U.filter fun i => S i).card) = (-1 : ℤ) ^ (((T ∆ U).filter fun i => S i).card) := by
  first
  | exact QuantumLTF.Majority.boolean_character_mul
  | exact QuantumLTF.Majority.boolean_character_mul ..
  | (intros; apply QuantumLTF.Majority.boolean_character_mul <;> assumption)
