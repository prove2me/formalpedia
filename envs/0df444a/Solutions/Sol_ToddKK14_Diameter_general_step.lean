-- Prove2me | solution 1 for ToddKK14.Diameter.general_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:48:06.033665+00:00
-- url     : https://prove2.me/submissions/ef51f6e3-357e-4c5a-918c-b463b15e399c

import Mathlib
set_option autoImplicit false

theorem solution (d n : ℕ) (hd : 4 ≤ d) (hnd : d + 8 ≤ n) (h2d : 2 * d ≤ n) :
    ((d : ℝ) - 1) ^ Real.logb 2 ((n : ℝ) - d) + 2 * (((n : ℝ) / 2 - d) ^ Real.logb 2 d) + 2
      ≤ (d : ℝ) ^ Real.logb 2 ((n : ℝ) - d) := by
  have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hnd' : (d : ℝ) + 8 ≤ n := by exact_mod_cast hnd
  have h2d' : 2 * (d : ℝ) ≤ n := by exact_mod_cast h2d
  have hdpos : (0 : ℝ) < d := by linarith
  set L : ℝ := Real.logb 2 ((n : ℝ) - d) with hL
  set t : ℝ := Real.logb 2 d with ht
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL3 : 3 ≤ L := by
    have h8 : Real.logb 2 8 = 3 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      norm_num
    rw [← h8]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
  have ht0 : 0 ≤ t := Real.logb_nonneg (by norm_num) (by linarith)
  -- second term: (n/2 - d)^t ≤ d^(L-1)
  have hY : ((n : ℝ) / 2 - d) ^ t ≤ (d : ℝ) ^ (L - 1) := by
    have h1 : ((n : ℝ) / 2 - d) ^ t ≤ (((n : ℝ) - d) / 2) ^ t :=
      Real.rpow_le_rpow (by linarith) (by linarith) ht0
    have hnd0 : (0 : ℝ) < ((n : ℝ) - d) / 2 := by linarith
    have h2 : (((n : ℝ) - d) / 2) ^ t = (d : ℝ) ^ (L - 1) := by
      rw [Real.rpow_def_of_pos hnd0, Real.rpow_def_of_pos hdpos]
      congr 1
      have hLe : L - 1 = Real.log (((n : ℝ) - d) / 2) / Real.log 2 := by
        rw [hL, Real.logb, Real.log_div (by linarith) (by norm_num)]
        field_simp
      rw [hLe, ht, Real.logb]
      ring
    rw [← h2]; exact h1
  -- main inequality
  set s : ℝ := L - 3 with hs
  have hs0 : 0 ≤ s := by linarith
  have hLs : L = 3 + s := by rw [hs]; ring
  have hL1 : L - 1 = 2 + s := by rw [hs]; ring
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by linarith
  have e1 : ((d : ℝ) - 1) ^ L = ((d : ℝ) - 1) ^ 3 * ((d : ℝ) - 1) ^ s := by
    rw [hLs, Real.rpow_add (by linarith)]
    norm_cast
  have e2 : (d : ℝ) ^ L = (d : ℝ) ^ 3 * (d : ℝ) ^ s := by
    rw [hLs, Real.rpow_add hdpos]
    norm_cast
  have e3 : (d : ℝ) ^ (L - 1) = (d : ℝ) ^ 2 * (d : ℝ) ^ s := by
    rw [hL1, Real.rpow_add hdpos]
    norm_cast
  have hu : (1 : ℝ) ≤ ((d : ℝ) - 1) ^ s := Real.one_le_rpow hd1 hs0
  have huv : ((d : ℝ) - 1) ^ s ≤ (d : ℝ) ^ s :=
    Real.rpow_le_rpow (by linarith) (by linarith) hs0
  set u : ℝ := ((d : ℝ) - 1) ^ s with hu_def
  set v : ℝ := (d : ℝ) ^ s with hv_def
  rw [e1, e2]
  have hY' : 2 * (((n : ℝ) / 2 - d) ^ t) ≤ 2 * ((d : ℝ) ^ 2 * v) := by
    have := hY; rw [e3] at this; linarith
  have hpoly : (d : ℝ) ^ 2 * ((d : ℝ) - 2) - ((d : ℝ) - 1) ^ 3 ≥ 5 := by nlinarith
  have hfinal : ((d : ℝ) - 1) ^ 3 * u + 2 * ((d : ℝ) ^ 2 * v) + 2 ≤ (d : ℝ) ^ 3 * v := by
    have h1 : (d : ℝ) ^ 2 * ((d : ℝ) - 2) * u ≤ (d : ℝ) ^ 2 * ((d : ℝ) - 2) * v :=
      mul_le_mul_of_nonneg_left huv (mul_nonneg (sq_nonneg _) (by linarith))
    nlinarith
  linarith
