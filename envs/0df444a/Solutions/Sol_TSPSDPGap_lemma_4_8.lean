-- Prove2me | solution 1 for TSPSDPGap.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:32:18.797309+00:00
-- url     : https://prove2.me/submissions/8d02fd46-d15c-417d-a5c2-965b3202ad5c

import Mathlib

theorem solution (n k : ℕ) (hn : Even n) (hk0 : 0 < k) (hkn : k < n) :
    ∑ j ∈ Finset.Icc 1 (n / 2), Real.cos (Real.pi * j * k / (n / 2 : ℕ)) =
      (-1 + (-1 : ℝ) ^ k) / 2 := by
  obtain ⟨d, hd⟩ : ∃ d, d = n / 2 := ⟨_, rfl⟩
  rw [← hd]
  have hn2 : n = 2 * d := by obtain ⟨r, hr⟩ := hn; omega
  have hd0 : 0 < d := by omega
  have hdR : (0:ℝ) < d := by exact_mod_cast hd0
  have hk2 : (k:ℝ) < 2 * d := by exact_mod_cast (by omega : k < 2 * d)
  have hkR : (0:ℝ) < k := by exact_mod_cast hk0
  obtain ⟨x, hx⟩ : ∃ x, x = Real.pi * k / d := ⟨_, rfl⟩
  have tele : ∀ m : ℕ, 2 * Real.sin (x / 2) * ∑ j ∈ Finset.Icc 1 m, Real.cos (j * x) =
      Real.sin ((m + 1 / 2) * x) - Real.sin (x / 2) := by
    intro m
    induction m with
    | zero =>
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      push_cast
      rw [show ((0:ℝ) + 1 / 2) * x = x / 2 by ring]
      ring
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
      push_cast
      have e1 : ((m:ℝ) + 1 + 1 / 2) * x = ((m:ℝ) + 1) * x + x / 2 := by ring
      have e2 : ((m:ℝ) + 1 / 2) * x = ((m:ℝ) + 1) * x - x / 2 := by ring
      rw [e1, e2, Real.sin_add, Real.sin_sub]
      ring
  have hsum : ∑ j ∈ Finset.Icc 1 d, Real.cos (Real.pi * j * k / d) =
      ∑ j ∈ Finset.Icc 1 d, Real.cos (j * x) :=
    Finset.sum_congr rfl (fun j _ => by rw [hx]; congr 1; ring)
  have hsx : Real.sin ((d + 1 / 2) * x) = (-1) ^ k * Real.sin (x / 2) := by
    have e : ((d:ℝ) + 1 / 2) * x = x / 2 + k * Real.pi := by
      rw [hx]; field_simp; ring
    rw [e, Real.sin_add_nat_mul_pi]
  have hpos : 0 < Real.sin (x / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · rw [hx]; positivity
    · rw [hx, div_div, div_lt_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
  rw [hsum]
  have h := tele d
  rw [hsx] at h
  have h2 : (2 * Real.sin (x / 2)) * ∑ j ∈ Finset.Icc 1 d, Real.cos (j * x) =
      (2 * Real.sin (x / 2)) * ((-1 + (-1 : ℝ) ^ k) / 2) := by
    rw [h]; ring
  exact mul_left_cancel₀ (by positivity) h2
