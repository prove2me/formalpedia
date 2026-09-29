-- Prove2me | solution 1 for apb_dvd_pow_add_pow
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T10:08:48.503242+00:00
-- url     : https://prove2.me/submissions/79fa5a54-8ace-45e1-aa7b-ebf5710b4fa5

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.GCD.Basic

-- For any odd natural n, (a+b) | (a^n+b^n) in ℕ.
theorem solution (n : ℕ) (h_odd : Odd n) (a b : ℕ) : (a+b) ∣ (a^n+b^n) := by
  have h_int : (a:ℤ)+b ∣ (a:ℤ)^n+b^n := by
    have h1 : (a:ℤ) - (-b) ∣ (a:ℤ)^n - (-b)^n := sub_dvd_pow_sub_pow _ _ _
    rw [h_odd.neg_pow, sub_neg_eq_add, sub_neg_eq_add] at h1
    exact h1
  exact_mod_cast (show ((a+b:ℕ):ℤ) ∣ ((a^n+b^n:ℕ):ℤ) by push_cast; exact h_int)
