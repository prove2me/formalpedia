-- Prove2me | solution 1 for ZeroOneSCO.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:37:22.245213+00:00
-- url     : https://prove2.me/submissions/600b8a55-0745-408e-854f-9601ae47fd0b

import Mathlib
import Definitions.Def_ZeroOneSCO_Columns

namespace Aux_ZeroOneSCO_eq_9
open ZeroOneSCO

theorem countP_ge (L : List ℝ) (hL : L.Pairwise (· ≥ ·)) (j : ℕ) (hj : j < L.length)
    (hpos : 0 < L[j]) : j + 1 ≤ L.countP (fun x => decide (0 < x)) := by
  have h1 : (L.take (j + 1)).countP (fun x => decide (0 < x)) = j + 1 := by
    rw [List.countP_eq_length.mpr]
    · rw [List.length_take]; omega
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      rw [List.getElem_take]
      simp only [List.length_take] at hi
      have hij : i ≤ j := by omega
      rcases Nat.lt_or_eq_of_le hij with h | h
      · have := List.pairwise_iff_getElem.mp hL i j (by omega) hj h
        simp only [decide_eq_true_eq]; linarith
      · subst h; simpa using hpos
  rw [← h1]
  exact (List.take_sublist _ _).countP_le

theorem countP_le (L : List ℝ) (hL : L.Pairwise (· ≥ ·)) (j : ℕ) (hj : j < L.length)
    (hnp : L[j] ≤ 0) : L.countP (fun x => decide (0 < x)) ≤ j := by
  rw [← List.take_append_drop j L, List.countP_append]
  have h2 : (L.drop j).countP (fun x => decide (0 < x)) = 0 := by
    rw [List.countP_eq_zero]
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    rw [List.getElem_drop]
    simp only [List.length_drop] at hi
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simpa using hnp
    · have := List.pairwise_iff_getElem.mp hL j (j + i) hj (by omega) (by omega)
      simp only [decide_eq_true_eq, not_lt]; linarith
  rw [h2, add_zero]
  exact (List.countP_le_length).trans (by rw [List.length_take]; omega)

theorem colPos_iff {M N : ℕ} [NeZero M] (Z : Mat M N) (n : Fin N) :
    0 < colPosNorm Z n ↔ 0 < colMax Z n := by
  unfold colPosNorm colMax
  rw [Real.sqrt_pos, Finset.lt_sup'_iff]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have : ∑ m, (max (Z m n) 0) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      rw [max_eq_right (hc m (Finset.mem_univ _))]; ring
    linarith
  · rintro ⟨m, _, hm⟩
    have hle : (max (Z m n) 0) ^ 2 ≤ ∑ m, (max (Z m n) 0) ^ 2 :=
      Finset.single_le_sum (f := fun m => (max (Z m n) 0) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ m)
    have : 0 < (max (Z m n) 0) ^ 2 := by
      rw [max_eq_left hm.le]; positivity
    linarith

theorem colPos_nonneg {M N : ℕ} (Z : Mat M N) (n : Fin N) : 0 ≤ colPosNorm Z n :=
  Real.sqrt_nonneg _

end Aux_ZeroOneSCO_eq_9

open ZeroOneSCO Aux_ZeroOneSCO_eq_9 in
theorem solution {M N : ℕ} [NeZero M] (Z : Mat M N) (s : ℕ) (hs : 0 < s) :
    (plusZero Z < s → rthLargest Z s = 0) ∧ (s ≤ plusZero Z → 0 < rthLargest Z s) := by
  set L := (Finset.univ.val.map (colPosNorm Z)).sort (· ≥ ·) with hLdef
  have hL : L.Pairwise (· ≥ ·) := Multiset.pairwise_sort _ _
  have hmem : ∀ x ∈ L, 0 ≤ x := by
    intro x hx
    rw [hLdef, Multiset.mem_sort, Multiset.mem_map] at hx
    obtain ⟨n, _, rfl⟩ := hx
    exact colPos_nonneg Z n
  have hcount : L.countP (fun x => decide (0 < x)) = plusZero Z := by
    have : (L : Multiset ℝ) = Finset.univ.val.map (colPosNorm Z) := Multiset.sort_eq _ _
    rw [← Multiset.coe_countP, this, Multiset.countP_map]
    unfold plusZero gammaPos
    rw [Finset.card_def, Finset.filter_val]
    congr 1
    apply Multiset.filter_congr
    intro n _
    simp [colPos_iff]
  have hr : rthLargest Z s = L.getD (s - 1) 0 := rfl
  constructor
  · intro h
    rw [hr]
    by_cases hj : s - 1 < L.length
    · rw [List.getD_eq_getElem _ _ hj]
      have h0 := hmem _ (List.getElem_mem hj)
      by_contra hne
      have := countP_ge L hL (s - 1) hj (lt_of_le_of_ne h0 (Ne.symm hne))
      omega
    · push_neg at hj
      rw [List.getD_eq_default _ _ hj]
  · intro h
    rw [hr]
    have hlen : plusZero Z ≤ L.length := by
      rw [← hcount]; exact List.countP_le_length
    have hj : s - 1 < L.length := by omega
    rw [List.getD_eq_getElem _ _ hj]
    by_contra hc
    push_neg at hc
    have := countP_le L hL (s - 1) hj hc
    omega
