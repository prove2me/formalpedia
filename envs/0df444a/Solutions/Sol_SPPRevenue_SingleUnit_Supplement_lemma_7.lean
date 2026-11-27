-- Prove2me | solution 1 for SPPRevenue.SingleUnit.Supplement.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:12:29.446923+00:00
-- url     : https://prove2.me/submissions/f401075b-32a4-4110-97bf-9eeb84709d4a

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Position

open SPPRevenue
open SPPRevenue.SingleUnit
open SPPRevenue.SingleUnit.Supplement

theorem solution {n : ℕ} (α : Fin n → ℝ) (hα : IsCTR α) (x : Fin n → Fin n → ℝ)
    (hx : ∀ j i, 0 ≤ x j i ∧ x j i ≤ 1) (hcap : ∀ j : Fin n, ∑ i, x j i ≤ (j : ℝ) + 1) :
    ClickIneq α (fun i => ∑ j, ctrGap α j * x j i) := by
      intro S
      set k := S.card with hk
      have hkn : k ≤ n := by
        have := Finset.card_le_univ S
        simpa using this
      set a : ℕ → ℝ := fun m => if h : m < n then α ⟨m, h⟩ else 0 with ha
      have hgap : ∀ j : Fin n, ctrGap α j = a j - a (j + 1) := by
        intro j
        simp only [ctrGap, ha, dif_pos j.isLt]
      have hgap_nn : ∀ j : Fin n, 0 ≤ ctrGap α j := by
        intro j
        unfold ctrGap
        split_ifs with h
        · have : α ⟨(j : ℕ) + 1, h⟩ ≤ α j := hα.1 (show j ≤ ⟨(j : ℕ) + 1, h⟩ from by
            rw [Fin.le_def]; simp)
          linarith
        · have := (hα.2 j).1
          linarith
      have ht : ∀ j : Fin n, ∑ i ∈ S, x j i ≤ min ((j : ℝ) + 1) (k : ℝ) := by
        intro j
        apply le_min
        · calc ∑ i ∈ S, x j i ≤ ∑ i, x j i :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                  (fun i _ _ => (hx j i).1)
            _ ≤ _ := hcap j
        · calc ∑ i ∈ S, x j i ≤ ∑ i ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hx j i).2)
            _ = k := by simp [hk]
      have hind : ∀ N : ℕ, ∑ j ∈ Finset.range N, (a j - a (j + 1)) * min ((j : ℝ) + 1) (k : ℝ)
          = ∑ m ∈ Finset.range (min N k), a m - a N * min (N : ℝ) (k : ℝ) := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [Finset.sum_range_succ, ih]
          by_cases hNk : N < k
          · have h1 : min N k = N := by omega
            have h2 : min (N + 1) k = N + 1 := by omega
            have h3 : min (N : ℝ) (k : ℝ) = N := by
              apply min_eq_left; exact_mod_cast hNk.le
            have h4 : min ((N : ℝ) + 1) (k : ℝ) = N + 1 := by
              apply min_eq_left; exact_mod_cast hNk
            rw [h1, h2, h3, Finset.sum_range_succ]
            push_cast
            rw [h4]
            ring
          · have h1 : min N k = k := by omega
            have h2 : min (N + 1) k = k := by omega
            have h3 : min (N : ℝ) (k : ℝ) = k := by
              apply min_eq_right; exact_mod_cast (not_lt.mp hNk)
            have h4 : min ((N : ℝ) + 1) (k : ℝ) = k := by
              apply min_eq_right
              have : (k : ℝ) ≤ N := by exact_mod_cast (not_lt.mp hNk)
              linarith
            rw [h1, h2, h3]
            push_cast
            rw [h4]
            ring
      have han : a n = 0 := by simp [ha]
      have hL : ∑ j : Fin n, ctrGap α j * min ((j : ℝ) + 1) (k : ℝ)
          = ∑ m ∈ Finset.range k, a m := by
        have := hind n
        rw [han, zero_mul, sub_zero, min_eq_right hkn] at this
        rw [← this]
        simp_rw [hgap]
        exact Fin.sum_univ_eq_sum_range (fun j => (a j - a (j + 1)) * min ((j : ℝ) + 1) (k : ℝ)) n
      have hR : ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), α j
          = ∑ m ∈ Finset.range k, a m := by
        rw [Finset.sum_filter]
        have : ∀ j : Fin n, (if (j : ℕ) < k then α j else 0) = (fun m : ℕ => if m < k then a m else 0) j := by
          intro j
          simp [ha, j.isLt]
        simp_rw [this]
        rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => if m < k then a m else 0) n, ← Finset.sum_filter]
        congr 1
        ext m
        simp
        omega
      calc ∑ i ∈ S, (fun i => ∑ j, ctrGap α j * x j i) i
          = ∑ j, ctrGap α j * ∑ i ∈ S, x j i := by
            simp only
            rw [Finset.sum_comm]
            simp_rw [Finset.mul_sum]
        _ ≤ ∑ j : Fin n, ctrGap α j * min ((j : ℝ) + 1) (k : ℝ) :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (ht j) (hgap_nn j))
        _ = _ := by rw [hL, hR]
