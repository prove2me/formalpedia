-- Prove2me | solution 2 for QuantumLTF.Majority.lemma_4_2_two_channel
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:14:42.379146+00:00
-- url     : https://prove2.me/submissions/26c8f6ec-d315-4164-97c6-f53327aaf0cf

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
namespace QuantumLTF.Majority

open scoped symmDiff

open Polynomial in
lemma kwo_coeff_one_sub_X_pow (a j : ℕ) :
    ((1 - X : ℤ[X]) ^ a).coeff j = (-1) ^ j * (a.choose j : ℤ) := by
  induction a generalizing j with
  | zero => cases j <;> simp [coeff_one]
  | succ a ih =>
    rw [pow_succ, mul_sub, mul_one, coeff_sub]
    cases j with
    | zero => simp [ih]
    | succ j =>
      rw [coeff_mul_X, ih, ih, Nat.choose_succ_succ']
      push_cast
      ring

open Polynomial in
lemma kwo_char {k : ℕ} (t a : ℕ) (A : Finset (Fin k)) (hAcard : A.card = a) :
    krawtchouk k t a = ∑ T ∈ (Finset.univ : Finset (Fin k)).powersetCard t,
      (-1 : ℤ) ^ ((T ∩ A).card) := by
  set c : Fin k → ℤ := fun i => if i ∈ A then -1 else 1 with hc
  have hP : ∏ i : Fin k, (1 + C (c i) * X) =
      ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset, C (∏ i ∈ T, c i) * X ^ T.card := by
    rw [Finset.prod_one_add]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_const, map_prod]
  have hak : a ≤ k := by
    rw [← hAcard]; simpa using Finset.card_le_univ A
  have hP2 : ∏ i : Fin k, (1 + C (c i) * X) = (1 - X) ^ a * (1 + X) ^ (k - a) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ A)]
    have e1 : ∏ i ∈ Finset.univ.filter (fun i => i ∈ A), (1 + C (c i) * X) =
        ∏ i ∈ Finset.univ.filter (fun i => i ∈ A), (1 - X : ℤ[X]) := by
      refine Finset.prod_congr rfl (fun i hi => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [hc, hi, if_true, map_neg, map_one]
      ring
    have e2 : ∏ i ∈ Finset.univ.filter (fun i => i ∉ A), (1 + C (c i) * X) =
        ∏ i ∈ Finset.univ.filter (fun i => i ∉ A), (1 + X : ℤ[X]) := by
      refine Finset.prod_congr rfl (fun i hi => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [hc, hi, if_false, map_one, one_mul]
    have hf1 : (Finset.univ.filter (fun i => i ∈ A)).card = a := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hAcard]
    have hf2 : (Finset.univ.filter (fun i => i ∉ A)).card = k - a := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
        (fun i => i ∈ A)
      rw [hf1, Finset.card_univ, Fintype.card_fin] at this
      omega
    rw [e1, e2, Finset.prod_const, Finset.prod_const, hf1, hf2]
  have key := congrArg (fun p : ℤ[X] => p.coeff t) (hP.symm.trans hP2)
  simp only [finsetSum_coeff, coeff_C_mul_X_pow] at key
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at key
  simp only [kwo_coeff_one_sub_X_pow, coeff_one_add_X_pow] at key
  unfold krawtchouk
  have lhs : ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
      (if t = T.card then ∏ i ∈ T, c i else 0) =
      ∑ T ∈ (Finset.univ : Finset (Fin k)).powersetCard t, (-1 : ℤ) ^ ((T ∩ A).card) := by
    rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    by_cases h : T.card = t
    · rw [if_pos h.symm, if_pos h, hc, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
        mul_one, Finset.filter_mem_eq_inter]
    · rw [if_neg (fun h' => h h'.symm), if_neg h]
  rw [← lhs, key]

lemma kwo_neg_one_pow_symmDiff {α : Type*} [DecidableEq α] (A B : Finset α) :
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

lemma kwo_total {k : ℕ} (W : Finset (Fin k)) :
    ∑ A ∈ (Finset.univ : Finset (Fin k)).powerset, (-1 : ℤ) ^ (W ∩ A).card =
      if W = ∅ then (2 : ℤ) ^ k else 0 := by
  set c : Fin k → ℤ := fun i => if i ∈ W then -1 else 1 with hc
  have h1 : ∀ A : Finset (Fin k), (-1 : ℤ) ^ (W ∩ A).card = ∏ i ∈ A, c i := by
    intro A
    rw [hc, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
      Finset.filter_mem_eq_inter, Finset.inter_comm]
  simp_rw [h1]
  rw [← Finset.prod_one_add]
  have h2 : ∀ i : Fin k, 1 + c i = if i ∈ W then 0 else 2 := by
    intro i; by_cases h : i ∈ W <;> simp [hc, h]
  simp_rw [h2]
  split_ifs with hW
  · subst hW; simp
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hW
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma kwo_orth_int (k t u : ℕ) :
    ∑ A ∈ (Finset.univ : Finset (Fin k)).powerset, krawtchouk k t A.card * krawtchouk k u A.card =
      if t = u then (2 : ℤ) ^ k * (k.choose t : ℤ) else 0 := by
  have hc : ∀ A : Finset (Fin k), krawtchouk k t A.card * krawtchouk k u A.card =
      ∑ T ∈ (Finset.univ : Finset (Fin k)).powersetCard t,
        ∑ U ∈ (Finset.univ : Finset (Fin k)).powersetCard u,
          (-1 : ℤ) ^ ((T ∆ U) ∩ A).card := by
    intro A
    rw [kwo_char t A.card A rfl, kwo_char u A.card A rfl, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun T _ => Finset.sum_congr rfl (fun U _ => ?_))
    rw [kwo_neg_one_pow_symmDiff]
    congr 2
    ext i
    simp only [Finset.mem_symmDiff, Finset.mem_inter]
    tauto
  simp_rw [hc]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin k)).powerset)]
  simp_rw [kwo_total]
  have he : ∀ T U : Finset (Fin k), (T ∆ U = ∅) ↔ T = U := by
    intro T U; rw [← Finset.bot_eq_empty, symmDiff_eq_bot]
  simp_rw [he]
  simp_rw [Finset.sum_ite_eq]
  by_cases htu : t = u
  · subst htu
    rw [if_pos rfl, Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · rw [if_neg htu]
    refine Finset.sum_eq_zero (fun T hT => ?_)
    rw [if_neg]
    intro hTu
    rw [Finset.mem_powersetCard] at hT hTu
    exact htu (hT.2.symm.trans hTu.2)

theorem krawtchouk_weighted_orthogonality : ∀ k : ℕ, ∀ t u : Fin (k+1), ∑ a : Fin (k+1), (k.choose a : ℝ) * (krawtchouk k t a : ℝ) * (krawtchouk k u a : ℝ) = if t = u then (2:ℝ)^k * (k.choose t : ℝ) else 0 := by
  intro k t u
  have h := kwo_orth_int k t u
  rw [Finset.sum_powerset_apply_card (fun m => krawtchouk k t m * krawtchouk k u m)] at h
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have h' := congrArg (fun z : ℤ => (z : ℝ)) h
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] at h'
  rw [← Fin.sum_univ_eq_sum_range] at h'
  have htu : (t = u) ↔ ((t : ℕ) = (u : ℕ)) := Fin.val_inj.symm
  by_cases hh : t = u
  · rw [if_pos hh]
    rw [if_pos (htu.mp hh)] at h'
    simp only [mul_assoc]
    rw [h']
    push_cast
    ring
  · rw [if_neg hh]
    rw [if_neg (fun e => hh (htu.mpr e))] at h'
    simp only [mul_assoc]
    rw [h']
    simp

lemma kwo_parseval (k : ℕ) (f : Fin (k+1) → ℝ) :
    ∑ a : Fin (k+1), (k.choose a : ℝ) * (∑ t : Fin (k+1), (krawtchouk k t a : ℝ) * f t) ^ 2 =
      (2:ℝ)^k * ∑ t : Fin (k+1), (k.choose t : ℝ) * f t ^ 2 := by
  have h1 : ∀ a : Fin (k+1), (k.choose a : ℝ) * (∑ t : Fin (k+1), (krawtchouk k t a : ℝ) * f t) ^ 2
      = ∑ t : Fin (k+1), ∑ u : Fin (k+1), f t * f u *
          ((k.choose a : ℝ) * (krawtchouk k t a : ℝ) * (krawtchouk k u a : ℝ)) := by
    intro a
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun t _ => Finset.sum_comm)]
  simp_rw [← Finset.mul_sum, krawtchouk_weighted_orthogonality]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  ring

theorem lemma_4_2_two_channel : ∀ k : ℕ, ∀ p q : Fin (k+1) → ℝ, let P : Fin (k+1) → ℝ := fun a => ∑ t : Fin (k+1), (krawtchouk k t a : ℝ) * p t; let Q : Fin (k+1) → ℝ := fun a => ∑ t : Fin (k+1), (krawtchouk k t a : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * q t); (1/(2:ℝ)^k) * ∑ a : Fin (k+1), (k.choose a : ℝ) * (P a^2 + Q a^2) = ∑ t : Fin (k+1), (k.choose t : ℝ) * (p t^2+q t^2) := by
  intro k p q P Q
  have hP := kwo_parseval k p
  have hQ := kwo_parseval k (fun t => (-1 : ℝ) ^ (t : ℕ) * q t)
  have hsq : ∀ t : Fin (k+1), ((-1 : ℝ) ^ (t : ℕ) * q t) ^ 2 = q t ^ 2 := by
    intro t
    rw [mul_pow, ← pow_mul, mul_comm (t : ℕ) 2, pow_mul]
    simp
  simp only [hsq] at hQ
  have e : ∑ a : Fin (k+1), (k.choose a : ℝ) * (P a^2 + Q a^2) =
      ∑ a : Fin (k+1), (k.choose a : ℝ) * P a ^ 2 + ∑ a : Fin (k+1), (k.choose a : ℝ) * Q a ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  rw [e]
  simp only [P, Q]
  rw [hP, hQ, ← mul_add, ← mul_assoc, one_div, inv_mul_cancel₀ (by positivity), one_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  ring

end QuantumLTF.Majority

theorem solution : ∀ k : ℕ, ∀ p q : Fin (k+1) → ℝ, let P : Fin (k+1) → ℝ := fun a => ∑ t : Fin (k+1), (QuantumLTF.Majority.krawtchouk k t a : ℝ) * p t; let Q : Fin (k+1) → ℝ := fun a => ∑ t : Fin (k+1), (QuantumLTF.Majority.krawtchouk k t a : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * q t); (1/(2:ℝ)^k) * ∑ a : Fin (k+1), (k.choose a : ℝ) * (P a^2 + Q a^2) = ∑ t : Fin (k+1), (k.choose t : ℝ) * (p t^2+q t^2) :=
  QuantumLTF.Majority.lemma_4_2_two_channel
