-- Prove2me | solution 1 for TsallisINF.Half.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T08:01:01.554456+00:00
-- url     : https://prove2.me/submissions/0e6e288d-b66f-4d84-bfa4-d10bd75d9670

import Mathlib
set_option autoImplicit false

lemma l15_key (b c x y : ℝ) (hb : 0 < b) (hc : 0 < c) (hy0 : 0 ≤ y) (hxy : y < x)
    (h1 : x ^ 2 - y ^ 2 = 1) (hD : 0 < b * y - c) :
    1 / (b * x ^ 3 - c * x ^ 2) ≤ 2 / (b * y - c) - 2 / (b * x - c) := by
  have hx : 0 < x := by linarith
  have hD2 : 0 < b * x - c := by nlinarith
  have hkey : b * y - c ≤ 2 * b * (x - y) * x ^ 2 := by
    have h2 : 1 ≤ 2 * x * (x - y) := by nlinarith
    have h3 : b * x ≤ 2 * b * (x - y) * x ^ 2 := by
      have : b * x * 1 ≤ b * x * (2 * x * (x - y)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      nlinarith
    nlinarith
  have e1 : b * x ^ 3 - c * x ^ 2 = x ^ 2 * (b * x - c) := by ring
  rw [e1, div_sub_div _ _ hD.ne' hD2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 < (b * x - c) := hD2
  have h4 : (b * y - c) * 1 ≤ (2 * b * (x - y) * x ^ 2) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right h4 (le_of_lt (mul_pos hD hD2)), mul_pos hD hD2]

lemma l15_term (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (s : ℕ) (hD : 0 < b * Real.sqrt (s : ℝ) - c) :
    1 / (b * ((s + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) - c * ((s + 1 : ℕ) : ℝ)) ≤
      2 / (b * Real.sqrt (s : ℝ) - c) - 2 / (b * Real.sqrt ((s + 1 : ℕ) : ℝ) - c) := by
  set x := Real.sqrt ((s + 1 : ℕ) : ℝ) with hx
  set y := Real.sqrt (s : ℝ) with hy
  have hx2 : x ^ 2 = ((s + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hy2 : y ^ 2 = (s : ℝ) := Real.sq_sqrt (by positivity)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have h1 : x ^ 2 - y ^ 2 = 1 := by rw [hx2, hy2]; push_cast; ring
  have hxy : y < x := Real.sqrt_lt_sqrt (by positivity) (by push_cast; linarith)
  have hp : ((s + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) = x ^ 3 := by
    rw [hx, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hp, ← hx2]
  have := l15_key b c x y hb hc hy0 hxy h1 hD
  convert this using 2

theorem solution (b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (T₀ T : ℕ) (hT : T₀ < T) (hden : c < b * Real.sqrt (T₀ : ℝ)) :
    (∑ t ∈ Finset.Icc (T₀ + 1) T,
      1 / (b * (t : ℝ) ^ (3 / 2 : ℝ) - c * (t : ℝ))) ≤
        2 / (b * Real.sqrt (T₀ : ℝ) - c) := by
  have main : ∀ n : ℕ, T₀ ≤ n →
      (∑ t ∈ Finset.Icc (T₀ + 1) n,
        1 / (b * (t : ℝ) ^ (3 / 2 : ℝ) - c * (t : ℝ))) ≤
        2 / (b * Real.sqrt (T₀ : ℝ) - c) - 2 / (b * Real.sqrt (n : ℝ) - c) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have hD : 0 < b * Real.sqrt (n : ℝ) - c := by
        have : Real.sqrt (T₀ : ℝ) ≤ Real.sqrt (n : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast hn)
        nlinarith
      rw [Finset.sum_Icc_succ_top (by omega)]
      have := l15_term b c hb hc n hD
      linarith
  have h := main T hT.le
  have hpos : 0 < b * Real.sqrt (T : ℝ) - c := by
    have : Real.sqrt (T₀ : ℝ) ≤ Real.sqrt (T : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hT.le)
    nlinarith
  have : 0 < 2 / (b * Real.sqrt (T : ℝ) - c) := by positivity
  linarith
