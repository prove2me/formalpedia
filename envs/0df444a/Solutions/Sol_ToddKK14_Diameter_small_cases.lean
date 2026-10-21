-- Prove2me | solution 1 for ToddKK14.Diameter.small_cases
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:58:36.609625+00:00
-- url     : https://prove2.me/submissions/4cbd2a9e-5be7-4ad6-b5df-753fc1cc2499

import Mathlib
import Definitions.Def_ToddKK14_Diameter_Bound

set_option autoImplicit false

namespace ToddKK14.Diameter

lemma logb_mul_le (x : ℝ) (hx : 0 < x) (u v : ℕ) (h : x ^ v ≤ 2 ^ u) :
    (v : ℝ) * Real.logb 2 x ≤ u := by
  have h1 : Real.logb 2 (x ^ v) ≤ Real.logb 2 (2 ^ u) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h1
  simpa using h1

lemma le_logb_mul (x : ℝ) (hx : 0 < x) (u v : ℕ) (h : 2 ^ u ≤ x ^ v) :
    (u : ℝ) ≤ (v : ℝ) * Real.logb 2 x := by
  have h1 : Real.logb 2 (2 ^ u) ≤ Real.logb 2 (x ^ v) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h1
  simpa using h1

lemma rpow_pow_key (x e : ℝ) (hx0 : 0 ≤ x) (v : ℕ) : (x ^ e) ^ v = x ^ (e * (v : ℝ)) := by
  rw [← Real.rpow_natCast (x ^ e) v, ← Real.rpow_mul hx0]

lemma tb_le (d n N u v : ℕ) (hd : 2 ≤ d) (hdn : d + 1 ≤ n) (hv : 0 < v)
    (h1 : d ^ v ≤ 2 ^ u) (h2 : (n - d) ^ u < (N + 1) ^ v) : toddBound d n ≤ N := by
  unfold toddBound
  have hx : (1 : ℝ) ≤ (n : ℝ) - d := by
    have : (d : ℝ) + 1 ≤ n := by exact_mod_cast hdn
    linarith
  have hx0 : (0 : ℝ) ≤ (n : ℝ) - d := by linarith
  have hlog : (v : ℝ) * Real.logb 2 d ≤ u := by
    apply logb_mul_le _ (by positivity)
    exact_mod_cast h1
  have hxe : ((n : ℝ) - d) = ((n - d : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
  have hlt : ((n : ℝ) - d) ^ Real.logb 2 d < (N : ℝ) + 1 := by
    by_contra hcon
    have hcon := not_lt.1 hcon
    have h3 : ((N : ℝ) + 1) ^ v ≤ (((n : ℝ) - d) ^ Real.logb 2 d) ^ v :=
      pow_le_pow_left₀ (by positivity) hcon v
    rw [rpow_pow_key _ _ hx0] at h3
    have h4 : ((n : ℝ) - d) ^ (Real.logb 2 d * (v : ℝ)) ≤ ((n : ℝ) - d) ^ (u : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by rw [mul_comm]; exact hlog)
    rw [Real.rpow_natCast] at h4
    have h5 : ((N : ℝ) + 1) ^ v ≤ ((n : ℝ) - d) ^ u := h3.trans h4
    rw [hxe] at h5
    have h6 : (N + 1) ^ v ≤ (n - d) ^ u := by exact_mod_cast h5
    omega
  have hnn : (0 : ℝ) ≤ ((n : ℝ) - d) ^ Real.logb 2 d := Real.rpow_nonneg hx0 _
  have := (Nat.floor_lt hnn (n := N + 1)).2 (by push_cast; exact hlt)
  omega

lemma tb_ge (d n N u v : ℕ) (hd : 2 ≤ d) (hdn : d + 1 ≤ n) (hv : 0 < v)
    (h1 : 2 ^ u ≤ d ^ v) (h2 : N ^ v ≤ (n - d) ^ u) : N ≤ toddBound d n := by
  unfold toddBound
  have hx : (1 : ℝ) ≤ (n : ℝ) - d := by
    have : (d : ℝ) + 1 ≤ n := by exact_mod_cast hdn
    linarith
  have hx0 : (0 : ℝ) ≤ (n : ℝ) - d := by linarith
  have hlog : (u : ℝ) ≤ (v : ℝ) * Real.logb 2 d := by
    apply le_logb_mul _ (by positivity)
    exact_mod_cast h1
  have hxe : ((n : ℝ) - d) = ((n - d : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
  apply Nat.le_floor
  by_contra hcon
  have hcon := not_le.1 hcon
  have h3 : (((n : ℝ) - d) ^ Real.logb 2 d) ^ v < (N : ℝ) ^ v :=
    pow_lt_pow_left₀ hcon (Real.rpow_nonneg hx0 _) (by omega)
  rw [rpow_pow_key _ _ hx0] at h3
  have h4 : ((n : ℝ) - d) ^ (u : ℝ) ≤ ((n : ℝ) - d) ^ (Real.logb 2 d * (v : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx (by rw [mul_comm]; exact hlog)
  rw [Real.rpow_natCast] at h4
  have h5 : ((n : ℝ) - d) ^ u < (N : ℝ) ^ v := lt_of_le_of_lt h4 h3
  rw [hxe] at h5
  have h6 : (n - d) ^ u < N ^ v := by exact_mod_cast h5
  omega

lemma tb_zero (d : ℕ) (hd : 2 ≤ d) : toddBound d d = 0 := by
  unfold toddBound
  have : Real.logb 2 (d : ℝ) ≠ 0 := by
    have : 0 < Real.logb 2 (d : ℝ) :=
      Real.logb_pos (by norm_num) (by exact_mod_cast hd)
    exact this.ne'
  simp [Real.zero_rpow this]

lemma tb_one (d : ℕ) (hd : 2 ≤ d) : toddBound d (d + 1) = 1 := by
  unfold toddBound
  simp

theorem small_cases' (d n : ℕ)
    (h : (d = 4 ∧ 8 ≤ n ∧ n ≤ 11) ∨ (d = 5 ∧ 10 ≤ n ∧ n ≤ 12) ∨ (d = 6 ∧ 12 ≤ n ∧ n ≤ 13) ∨
      (d = 7 ∧ n = 14)) :
    toddBound (d - 1) (n - 1) + 2 * toddBound d (n / 2) + 2 ≤ toddBound d n := by
  rcases h with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, rfl⟩
  · interval_cases n
    · -- d=4, n=8
      have h1 : toddBound 3 7 ≤ 10 := tb_le 3 7 10 5 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have h2 : toddBound 4 4 = 0 := tb_zero 4 (by norm_num)
      have h3 : 16 ≤ toddBound 4 8 := tb_ge 4 8 16 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      show toddBound 3 7 + 2 * toddBound 4 4 + 2 ≤ toddBound 4 8
      omega
  
    · -- d=4, n=9
      have h1 : toddBound 3 8 ≤ 14 := tb_le 3 8 14 5 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have h2 : toddBound 4 4 = 0 := tb_zero 4 (by norm_num)
      have h3 : 25 ≤ toddBound 4 9 := tb_ge 4 9 25 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      show toddBound 3 8 + 2 * toddBound 4 4 + 2 ≤ toddBound 4 9
      omega
  
    · -- d=4, n=10
      have h1 : toddBound 3 9 ≤ 19 := tb_le 3 9 19 5 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have h2 : toddBound 4 5 = 1 := tb_one 4 (by norm_num)
      have h3 : 36 ≤ toddBound 4 10 := tb_ge 4 10 36 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      show toddBound 3 9 + 2 * toddBound 4 5 + 2 ≤ toddBound 4 10
      omega
  
    · -- d=4, n=11
      have h1 : toddBound 3 10 ≤ 25 := tb_le 3 10 25 5 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have h2 : toddBound 4 5 = 1 := tb_one 4 (by norm_num)
      have h3 : 49 ≤ toddBound 4 11 := tb_ge 4 11 49 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      show toddBound 3 10 + 2 * toddBound 4 5 + 2 ≤ toddBound 4 11
      omega
  
  · interval_cases n
    · -- d=5, n=10
      have h1 : toddBound 4 9 ≤ 25 := tb_le 4 9 25 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have h2 : toddBound 5 5 = 0 := tb_zero 5 (by norm_num)
      have h3 : 37 ≤ toddBound 5 10 := tb_ge 5 10 37 9 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      show toddBound 4 9 + 2 * toddBound 5 5 + 2 ≤ toddBound 5 10
      omega
  
    · -- d=5, n=11
      have h1 : toddBound 4 10 ≤ 36 := tb_le 4 10 36 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have h2 : toddBound 5 5 = 0 := tb_zero 5 (by norm_num)
      have h3 : 56 ≤ toddBound 5 11 := tb_ge 5 11 56 9 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      show toddBound 4 10 + 2 * toddBound 5 5 + 2 ≤ toddBound 5 11
      omega
  
    · -- d=5, n=12
      have h1 : toddBound 4 11 ≤ 49 := tb_le 4 11 49 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have h2 : toddBound 5 6 = 1 := tb_one 5 (by norm_num)
      have h3 : 79 ≤ toddBound 5 12 := tb_ge 5 12 79 9 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      show toddBound 4 11 + 2 * toddBound 5 6 + 2 ≤ toddBound 5 12
      omega
  
  · interval_cases n
    · -- d=6, n=12
      have h1 : toddBound 5 11 ≤ 65 := tb_le 5 11 65 7 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have h2 : toddBound 6 6 = 0 := tb_zero 6 (by norm_num)
      have h3 : 88 ≤ toddBound 6 12 := tb_ge 6 12 88 5 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      show toddBound 5 11 + 2 * toddBound 6 6 + 2 ≤ toddBound 6 12
      omega
  
    · -- d=6, n=13
      have h1 : toddBound 5 12 ≤ 93 := tb_le 5 12 93 7 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have h2 : toddBound 6 6 = 0 := tb_zero 6 (by norm_num)
      have h3 : 129 ≤ toddBound 6 13 := tb_ge 6 13 129 5 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      show toddBound 5 12 + 2 * toddBound 6 6 + 2 ≤ toddBound 6 13
      omega
  
  · -- d=7, n=14
    have h1 : toddBound 6 13 ≤ 157 := tb_le 6 13 157 13 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h2 : toddBound 7 7 = 0 := tb_zero 7 (by norm_num)
    have h3 : 210 ≤ toddBound 7 14 := tb_ge 7 14 210 11 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    show toddBound 6 13 + 2 * toddBound 7 7 + 2 ≤ toddBound 7 14
    omega

end ToddKK14.Diameter

theorem solution (d n : ℕ)
    (h : (d = 4 ∧ 8 ≤ n ∧ n ≤ 11) ∨ (d = 5 ∧ 10 ≤ n ∧ n ≤ 12) ∨ (d = 6 ∧ 12 ≤ n ∧ n ≤ 13) ∨
      (d = 7 ∧ n = 14)) :
    ToddKK14.Diameter.toddBound (d - 1) (n - 1) + 2 * ToddKK14.Diameter.toddBound d (n / 2) + 2 ≤ ToddKK14.Diameter.toddBound d n :=
  ToddKK14.Diameter.small_cases' d n h
