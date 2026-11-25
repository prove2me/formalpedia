-- Prove2me | solution 1 for SZ.exists_eventually_composite_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:36.859374+00:00
-- url     : https://prove2.me/submissions/916e4d91-0920-4990-9302-badce9e5d64e

import Definitions.Def_SZ_SliceHygiene
import Mathlib.Tactic.Push
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_ThmC
import Theorems.Thm_SZ_exists_dvd_floor_sqrt

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution (p : ℤ) (m : ℕ) (hp : 2 ≤ p) (hm : 3 ≤ m)
    (hns : ¬ IsSquare m)
    (hcase : (p ∣ (m : ℤ) - 1 ∧ p ^ 2 ≤ (m : ℤ)) ∨
      (p ∣ (m : ℤ) ∧ (p : ℝ) * ((m : ℝ) - 1) < ((m : ℝ) - (p : ℝ)) * (1 + Real.sqrt m))) :
    ∃ ξ : ℝ, 0 < ξ ∧ (∀ n : ℕ, 1 ≤ n → p ∣ ⌊ξ * Real.sqrt m ^ n⌋) ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        ∃ a b : ℤ, 1 < a ∧ 1 < b ∧ ⌊ξ * Real.sqrt m ^ n⌋ = a * b := by
  obtain ⟨ξ, hξ, hdvd⟩ := exists_dvd_floor_sqrt p m hp hm hns hcase
  have hmr : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hs1 : 1 < Real.sqrt m := by
    have h : Real.sqrt 1 < Real.sqrt m := Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    rwa [Real.sqrt_one] at h
  obtain ⟨N0, hN0⟩ := pow_unbounded_of_one_lt (((p : ℝ) + 1) / ξ) hs1
  have hbig : (p : ℝ) + 1 < ξ * Real.sqrt m ^ N0 := by
    have := (div_lt_iff₀ hξ).mp hN0
    linarith
  refine ⟨ξ, hξ, hdvd, max N0 1, le_max_right _ _, fun n hn => ?_⟩
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hmono : Real.sqrt m ^ N0 ≤ Real.sqrt m ^ n :=
    pow_le_pow_right₀ hs1.le hn0
  have hval : (p : ℝ) + 1 < ξ * Real.sqrt m ^ n := by
    have := mul_le_mul_of_nonneg_left hmono hξ.le
    linarith
  have hfl : p + 1 ≤ ⌊ξ * Real.sqrt m ^ n⌋ := Int.le_floor.mpr (by push_cast; linarith)
  obtain ⟨b, hb⟩ := hdvd n hn1
  have hb1 : 1 < b := by
    by_contra hcon
    push Not at hcon
    have h1 : p * b ≤ p * 1 := mul_le_mul_of_nonneg_left hcon (by omega)
    rw [← hb] at h1
    omega
  exact ⟨p, b, by omega, hb1, hb⟩
end SZ
