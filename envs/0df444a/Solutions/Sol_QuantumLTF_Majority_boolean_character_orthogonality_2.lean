-- Prove2me | solution 2 for QuantumLTF.Majority.boolean_character_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:06:02.349727+00:00
-- url     : https://prove2.me/submissions/5de58fce-4519-41ff-9c16-7c4baafb5693

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

lemma qltf_char_prod {k : ℕ} (T : Finset (Fin k)) (S : Qubits k) :
    (-1 : ℤ) ^ ((T.filter fun i => S i).card) =
      ∏ i, (if i ∈ T then (if S i then (-1 : ℤ) else 1) else 1) := by
  rw [Finset.prod_ite_mem, Finset.univ_inter, ← Finset.prod_filter, Finset.prod_const]

lemma qltf_total : ∀ k : ℕ, ∀ T : Finset (Fin k), ∑ S : Qubits k, (-1 : ℤ) ^ ((T.filter fun i => S i).card) = if T = ∅ then (2 : ℤ)^k else 0 := by
  intro k T
  simp_rw [qltf_char_prod]
  rw [← Fintype.prod_sum (fun (i : Fin k) (b : Bool) =>
    (if i ∈ T then (if b then (-1 : ℤ) else 1) else 1))]
  have hs : ∀ i : Fin k, (∑ b : Bool, (if i ∈ T then (if b then (-1 : ℤ) else 1) else 1)) =
      if i ∈ T then 0 else 2 := by
    intro i
    by_cases h : i ∈ T <;> simp [h]
  simp_rw [hs]
  split_ifs with hT
  · subst hT
    simp
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem boolean_character_orthogonality : ∀ k : ℕ, ∀ T U : Finset (Fin k), ∑ S : Qubits k, (-1 : ℤ) ^ ((T.filter fun i => S i).card) * (-1 : ℤ) ^ ((U.filter fun i => S i).card) = if T = U then (2 : ℤ)^k else 0 := by
  intro k T U
  have h : ∀ S : Qubits k, (-1 : ℤ) ^ ((T.filter fun i => S i).card) *
      (-1 : ℤ) ^ ((U.filter fun i => S i).card) =
      (-1 : ℤ) ^ (((T ∆ U).filter fun i => S i).card) := by
    intro S
    rw [qltf_neg_one_pow_symmDiff]
    congr 2
    ext i
    simp only [Finset.mem_symmDiff, Finset.mem_filter]
    tauto
  simp_rw [h]
  rw [qltf_total]
  have he : T ∆ U = ∅ ↔ T = U := by
    rw [← Finset.bot_eq_empty, symmDiff_eq_bot]
  by_cases hTU : T = U
  · simp [hTU]
  · rw [if_neg (fun h' => hTU (he.mp h')), if_neg hTU]

end QuantumLTF.Majority

open QAlgorithms in
theorem solution : ∀ k : ℕ, ∀ T U : Finset (Fin k), ∑ S : Qubits k, (-1 : ℤ) ^ ((T.filter fun i => S i).card) * (-1 : ℤ) ^ ((U.filter fun i => S i).card) = if T = U then (2 : ℤ)^k else 0 := by
  first
  | exact QuantumLTF.Majority.boolean_character_orthogonality
  | exact QuantumLTF.Majority.boolean_character_orthogonality ..
  | (intros; apply QuantumLTF.Majority.boolean_character_orthogonality <;> assumption)
