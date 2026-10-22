-- Prove2me | solution 1 for UnknownProphet.NoSamples.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:00:36.587443+00:00
-- url     : https://prove2.me/submissions/0aed6f64-76d0-46c3-918a-b0b956ce3a1d

import Mathlib
import Definitions.Def_UnknownProphet_NoSamples_Model

namespace UnknownProphet.NoSamples

open Finset

lemma eq1_pow_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    (1 - a) ^ n ≤ 1 - n * a + ((n : ℝ) * (n - 1) / 2) * a ^ 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    have h1 : 0 ≤ 1 - a := by linarith
    calc (1 - a) ^ m * (1 - a) ≤ (1 - m * a + ((m : ℝ) * (m - 1) / 2) * a ^ 2) * (1 - a) :=
          mul_le_mul_of_nonneg_right ih h1
      _ ≤ 1 - ((m + 1 : ℕ) : ℝ) * a + (((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) - 1) / 2) * a ^ 2 := by
          push_cast
          have hm : (0 : ℝ) ≤ m := by positivity
          have : 0 ≤ ((m : ℝ) * (m - 1) / 2) * a ^ 3 ∨ True := Or.inr trivial
          rcases Nat.eq_zero_or_pos m with h0 | hpos
          · subst h0; simp
          · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hpos
            have : 0 ≤ ((m : ℝ) * (m - 1) / 2) * a ^ 3 := by
              have : 0 ≤ (m : ℝ) * (m - 1) := by nlinarith
              positivity
            nlinarith

theorem eq_1_main (n : ℕ) (hn : 1 ≤ n) (F : FinDist)
    (v : Fin (n ^ 3) → ℝ) (u : ℝ) (hF : IsHardInstance n F v u) :
    probMaxEq F n u * u ≤ expMax F n ∧
      probMaxEq F n u = 1 - (1 - 1 / (n : ℝ) ^ 2) ^ n ∧
      (1 - 1 / (2 * (n : ℝ))) / n ≤ probMaxEq F n u := by
  classical
  obtain ⟨hvinj, hv0, hvu, hvle, hsupp, hwv, hwu⟩ := hF
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hu_mem : u ∈ F.supp := by rw [hsupp]; exact Finset.mem_insert_self _ _
  have hu0 : 0 ≤ u := F.supp_nonneg u hu_mem
  have hle_u : ∀ y ∈ F.supp, y ≤ u := by
    intro y hy
    rw [hsupp] at hy
    rcases Finset.mem_insert.mp hy with h | h
    · exact h.le
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
      have h3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hnR
      have := hvle j
      nlinarith [hv0 j]
  -- characterization of the max
  have hmax : ∀ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
      ((⨆ i, x i) = u ↔ ∃ j, x j = u) := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx
    constructor
    · intro h
      obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := x)
      exact ⟨i, hi.trans h⟩
    · rintro ⟨j, hj⟩
      apply le_antisymm
      · exact ciSup_le (fun i => hle_u _ (hx i))
      · rw [← hj]; exact le_ciSup (Finite.bddAbove_range x) j
  have hwnn : ∀ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp), 0 ≤ iidWeight F x := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx
    exact Finset.prod_nonneg (fun j _ => F.w_nonneg _ (hx j))
  have hsupnn : ∀ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp), 0 ≤ ⨆ i, x i := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx
    exact le_trans (F.supp_nonneg _ (hx ⟨0, hn⟩)) (le_ciSup (Finite.bddAbove_range x) _)
  -- part (a)
  have partA : probMaxEq F n u * u ≤ expMax F n := by
    unfold probMaxEq expMax
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x hx
    split_ifs with h
    · rw [h]
    · rw [zero_mul]; exact mul_nonneg (hwnn x hx) (hsupnn x hx)
  -- part (b)
  have htot : ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp), iidWeight F x = 1 := by
    unfold iidWeight
    rw [Finset.sum_prod_piFinset F.supp (fun _ y => F.w y), F.w_sum]
    simp
  have hnone : ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
      (if ∀ j, x j ≠ u then iidWeight F x else 0) = (1 - F.w u) ^ n := by
    have : ∀ x : Fin n → ℝ, (if ∀ j, x j ≠ u then iidWeight F x else 0) =
        ∏ j, (if x j ≠ u then F.w (x j) else 0) := by
      intro x
      unfold iidWeight
      split_ifs with h
      · apply Finset.prod_congr rfl
        intro j _
        rw [if_pos (h j)]
      · push Not at h
        obtain ⟨j, hj⟩ := h
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        rw [if_neg (not_not.mpr hj)]
    simp_rw [this]
    rw [Finset.sum_prod_piFinset F.supp (fun _ y => if y ≠ u then F.w y else 0)]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have := Finset.sum_filter_add_sum_filter_not F.supp (fun y => y ≠ u) F.w
    rw [F.w_sum] at this
    have h2 : ∑ y ∈ F.supp with ¬ y ≠ u, F.w y = F.w u := by
      have : F.supp.filter (fun y => ¬ y ≠ u) = {u} := by
        ext y; simp only [Finset.mem_filter, not_not, Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro rfl; exact ⟨hu_mem, rfl⟩
      rw [this, Finset.sum_singleton]
    linarith
  have partB : probMaxEq F n u = 1 - (1 - 1 / (n : ℝ) ^ 2) ^ n := by
    rw [← hwu, ← hnone, ← htot]
    unfold probMaxEq
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : ∃ j, x j = u
    · have h' : (⨆ i, x i) = u := (hmax x hx).mpr h
      have h'' : ¬ ∀ j, x j ≠ u := by push Not; exact h
      rw [if_pos h', if_neg h'']
      ring
    · have h' : ¬ (⨆ i, x i) = u := fun hh => h ((hmax x hx).mp hh)
      have h'' : ∀ j, x j ≠ u := by push Not at h; exact h
      rw [if_neg h', if_pos h'']
      ring
  refine ⟨partA, partB, ?_⟩
  rw [partB]
  have ha0 : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by positivity
  have ha1 : 1 / (n : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hp := eq1_pow_le (1 / (n : ℝ) ^ 2) ha0 ha1 n
  have hnpos : (0 : ℝ) < n := by linarith
  have key : (1 - 1 / (2 * (n : ℝ))) / n ≤
      n * (1 / (n : ℝ) ^ 2) - ((n : ℝ) * (n - 1) / 2) * (1 / (n : ℝ) ^ 2) ^ 2 := by
    rw [div_le_iff₀ hnpos]
    field_simp
    nlinarith
  linarith

end UnknownProphet.NoSamples

open UnknownProphet.NoSamples in
theorem solution (n : ℕ) (hn : 1 ≤ n) (F : FinDist)
    (v : Fin (n ^ 3) → ℝ) (u : ℝ) (hF : IsHardInstance n F v u) :
    probMaxEq F n u * u ≤ expMax F n ∧
      probMaxEq F n u = 1 - (1 - 1 / (n : ℝ) ^ 2) ^ n ∧
      (1 - 1 / (2 * (n : ℝ))) / n ≤ probMaxEq F n u :=
  eq_1_main n hn F v u hF
