-- Prove2me | solution 1 for ShamirLLR.eq_75_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:42:54.130192+00:00
-- url     : https://prove2.me/submissions/543bc085-f35b-4167-9319-5683ce9aea3b

import Mathlib

open Real Finset

theorem solution (m t : ℕ) (α x : ℝ) (hα : 0 < α) (hα2 : α ≤ 1 / 2)
    (ht : (t : ℝ) ≤ α * m) (hx : 1 ≤ x) :
    ∑ j ∈ Finset.range t, (m.choose j : ℝ) * x ^ j ≤
      (2 : ℝ) ^ ((m : ℝ) * (Real.binEntropy α / Real.log 2 + α * Real.logb 2 x)) := by
  have hx0 : 0 < x := by linarith
  have h1α : 0 < 1 - α := by linarith
  set l : ℝ := α / ((1 - α) * x) with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l ≤ 1 := by
    rw [hl, div_le_one (by positivity)]
    nlinarith
  have hlx : l * x = α / (1 - α) := by
    rw [hl]; field_simp
  have hP : 0 < l ^ (α * m) := Real.rpow_pos_of_pos hl0 _
  -- each term
  have hterm : ∀ j ∈ range t, (m.choose j : ℝ) * x ^ j ≤
      (m.choose j : ℝ) * (l * x) ^ j / l ^ (α * m) := by
    intro j hj
    have hj' : (j : ℝ) ≤ α * m := by
      have := mem_range.mp hj
      have : (j : ℝ) < t := by exact_mod_cast this
      linarith
    have hpow : l ^ (α * m) ≤ l ^ j := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hl0 hl1 hj'
    rw [le_div_iff₀ hP, mul_pow]
    have hc : 0 ≤ (m.choose j : ℝ) * x ^ j := by positivity
    calc (m.choose j : ℝ) * x ^ j * l ^ (α * m) ≤ (m.choose j : ℝ) * x ^ j * l ^ j :=
          mul_le_mul_of_nonneg_left hpow hc
      _ = (m.choose j : ℝ) * (l ^ j * x ^ j) := by ring
  have htm : t ≤ m + 1 := by
    have : (t : ℝ) ≤ m := by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have : t ≤ m := by exact_mod_cast this
    omega
  calc ∑ j ∈ range t, (m.choose j : ℝ) * x ^ j
      ≤ ∑ j ∈ range t, (m.choose j : ℝ) * (l * x) ^ j / l ^ (α * m) := sum_le_sum hterm
    _ ≤ ∑ j ∈ range (m + 1), (m.choose j : ℝ) * (l * x) ^ j / l ^ (α * m) := by
        apply sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr htm)
        intro i _ _; positivity
    _ = (1 + l * x) ^ m / l ^ (α * m) := by
        rw [← sum_div, show (1 + l * x) = l * x + 1 by ring, add_pow]
        congr 1; apply sum_congr rfl; intro j _; simp only [one_pow]; ring
    _ = (2 : ℝ) ^ ((m : ℝ) * (Real.binEntropy α / Real.log 2 + α * Real.logb 2 x)) := by
        have hb : 1 + l * x = (1 - α)⁻¹ := by rw [hlx]; field_simp; ring
        rw [hb, Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos hl0,
          ← Real.exp_log (by positivity : (0:ℝ) < (1 - α)⁻¹ ^ m), Real.log_pow, Real.log_inv,
          ← Real.exp_sub]
        congr 1
        have hlog : Real.log l = Real.log α - Real.log (1 - α) - Real.log x := by
          rw [hl, Real.log_div hα.ne' (by positivity), Real.log_mul h1α.ne' hx0.ne']; ring
        rw [hlog, Real.binEntropy, Real.logb]
        have h2 : Real.log 2 ≠ 0 := by positivity
        field_simp
        simp only [one_div, Real.log_inv] at *
        ring
