-- Prove2me | solution 1 for VolunteerNotify.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:27:23.793524+00:00
-- url     : https://prove2.me/submissions/30cfa75b-1156-4cca-8c71-5c01314874b1

import Mathlib

theorem solution (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : c ∈ Set.Ioc (0 : ℝ) 1) :
    1 - 1 / Real.exp 1 < (1 - (1 - c / n) ^ n) / c := by
  obtain ⟨hc0, hc1⟩ := hc
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hx : c / n ≠ 0 := div_ne_zero hc0.ne' hn0
  have h1 : 1 - c / n < Real.exp (-(c / n)) := by
    have := Real.add_one_lt_exp (neg_ne_zero.2 hx)
    linarith
  have h0 : 0 ≤ 1 - c / n := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have h2 : (1 - c / n) ^ n < Real.exp (-(c / n)) ^ n :=
    pow_lt_pow_left₀ h1 h0 (by omega)
  have h3 : Real.exp (-(c / n)) ^ n = Real.exp (-c) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have key := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-1:ℝ))
    (show (0:ℝ) ≤ 1 - c by linarith) hc0.le (show (1 - c) + c = 1 by ring)
  have e1 : (1 - c) • (0:ℝ) + c • (-1:ℝ) = -c := by simp
  rw [e1] at key
  simp only [smul_eq_mul, Real.exp_zero, mul_one] at key
  have he : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
  rw [he] at key
  rw [lt_div_iff₀ hc0]
  nlinarith
