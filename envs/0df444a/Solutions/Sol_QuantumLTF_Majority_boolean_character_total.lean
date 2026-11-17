-- Prove2me | solution 1 for QuantumLTF.Majority.boolean_character_total
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:06:01.614028+00:00
-- url     : https://prove2.me/submissions/66d4bd37-7f7b-412c-bcb0-ee74be792aba

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
namespace QuantumLTF.Majority

open QAlgorithms

lemma qltf_char_prod {k : ℕ} (T : Finset (Fin k)) (S : Qubits k) :
    (-1 : ℤ) ^ ((T.filter fun i => S i).card) =
      ∏ i, (if i ∈ T then (if S i then (-1 : ℤ) else 1) else 1) := by
  rw [Finset.prod_ite_mem, Finset.univ_inter, ← Finset.prod_filter, Finset.prod_const]

theorem boolean_character_total : ∀ k : ℕ, ∀ T : Finset (Fin k), ∑ S : Qubits k, (-1 : ℤ) ^ ((T.filter fun i => S i).card) = if T = ∅ then (2 : ℤ)^k else 0 := by
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

end QuantumLTF.Majority

open QAlgorithms in
theorem solution : ∀ k : ℕ, ∀ T : Finset (Fin k), ∑ S : Qubits k, (-1 : ℤ) ^ ((T.filter fun i => S i).card) = if T = ∅ then (2 : ℤ)^k else 0 := by
  first
  | exact QuantumLTF.Majority.boolean_character_total
  | exact QuantumLTF.Majority.boolean_character_total ..
  | (intros; apply QuantumLTF.Majority.boolean_character_total <;> assumption)
