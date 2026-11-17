-- Prove2me | solution 1 for QuantumLTF.Majority.krawtchouk_as_character_sum
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:10:17.090517+00:00
-- url     : https://prove2.me/submissions/c5941bbf-6a55-46b8-b177-6003e0431304

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
namespace QuantumLTF.Majority

open Polynomial in
lemma kr_coeff_one_sub_X_pow (a j : ℕ) :
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
theorem krawtchouk_as_character_sum : ∀ k : ℕ, ∀ t a : Fin (k+1), (krawtchouk k t a : ℤ) = ∑ T ∈ (Finset.univ : Finset (Fin k)).powersetCard (t : ℕ), (-1 : ℤ) ^ ((T ∩ (Finset.univ.filter fun i : Fin k => (i : ℕ) < (a : ℕ))).card) := by
  intro k t a
  set A := (Finset.univ.filter fun i : Fin k => (i : ℕ) < (a : ℕ)) with hA
  set c : Fin k → ℤ := fun i => if i ∈ A then -1 else 1 with hc
  have hP : ∏ i : Fin k, (1 + C (c i) * X) =
      ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset, C (∏ i ∈ T, c i) * X ^ T.card := by
    rw [Finset.prod_one_add]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_const, map_prod]
  have hAcard : A.card = (a : ℕ) := by
    rw [hA, Fin.card_filter_val_lt]
    have := a.isLt
    omega
  have hP2 : ∏ i : Fin k, (1 + C (c i) * X) = (1 - X) ^ (a : ℕ) * (1 + X) ^ (k - a) := by
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
    have hf1 : (Finset.univ.filter (fun i => i ∈ A)).card = (a : ℕ) := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hAcard]
    have hf2 : (Finset.univ.filter (fun i => i ∉ A)).card = k - a := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
        (fun i => i ∈ A)
      rw [hf1, Finset.card_univ, Fintype.card_fin] at this
      omega
    rw [e1, e2, Finset.prod_const, Finset.prod_const, hf1, hf2]
  have key := congrArg (fun p : ℤ[X] => p.coeff (t : ℕ)) (hP.symm.trans hP2)
  simp only [finsetSum_coeff, coeff_C_mul_X_pow] at key
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at key
  simp only [kr_coeff_one_sub_X_pow, coeff_one_add_X_pow] at key
  unfold krawtchouk
  have lhs : ∑ T ∈ (Finset.univ : Finset (Fin k)).powerset,
      (if (t : ℕ) = T.card then ∏ i ∈ T, c i else 0) =
      ∑ T ∈ (Finset.univ : Finset (Fin k)).powersetCard (t : ℕ), (-1 : ℤ) ^ ((T ∩ A).card) := by
    rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    by_cases h : T.card = (t : ℕ)
    · rw [if_pos h.symm, if_pos h, hc, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
        mul_one, Finset.filter_mem_eq_inter]
    · rw [if_neg (fun h' => h h'.symm), if_neg h]
  rw [← lhs, key]

end QuantumLTF.Majority

theorem solution : ∀ k : ℕ, ∀ t a : Fin (k+1), (QuantumLTF.Majority.krawtchouk k t a : ℤ) = ∑ T ∈ (Finset.univ : Finset (Fin k)).powersetCard (t : ℕ), (-1 : ℤ) ^ ((T ∩ (Finset.univ.filter fun i : Fin k => (i : ℕ) < (a : ℕ))).card) :=
  QuantumLTF.Majority.krawtchouk_as_character_sum
