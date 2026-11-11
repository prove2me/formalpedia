-- Prove2me | solution 1 for QuantumXoP.Security.lemma_6_13
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T21:26:25.159202+00:00
-- url     : https://prove2.me/submissions/a93c9e09-340a-4bcb-8134-aec80efb607e

import Mathlib

/-- Lemma 6.13 (p. 31): for `x, y ∈ ℝ`, `|(x + y)^r − x^r| ≤ r |y| (|x| + |y|)^{r−1}`. -/
theorem solution (r : ℕ) (x y : ℝ) :
    |(x + y) ^ r - x ^ r| ≤ r * |y| * (|x| + |y|) ^ (r - 1) := by
  have key : (x + y) ^ r - x ^ r = ((x + y) - x) * ∑ i ∈ Finset.range r, (x + y) ^ i * x ^ (r - 1 - i) := by
    have := (Commute.all (x + y) x).geom_sum₂_mul r
    rw [← this]; ring
  rw [key, abs_mul]
  have hy : |(x + y) - x| = |y| := by ring_nf
  rw [hy]
  have hs : |∑ i ∈ Finset.range r, (x + y) ^ i * x ^ (r - 1 - i)| ≤ r * (|x| + |y|) ^ (r - 1) := by
    calc _ ≤ ∑ i ∈ Finset.range r, |(x + y) ^ i * x ^ (r - 1 - i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range r, (|x| + |y|) ^ (r - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ r - 1 := by have := Finset.mem_range.mp hi; omega
        rw [abs_mul, abs_pow, abs_pow]
        have h1 : |x + y| ≤ |x| + |y| := abs_add_le x y
        have h2 : |x| ≤ |x| + |y| := by linarith [abs_nonneg y]
        calc |x + y| ^ i * |x| ^ (r - 1 - i) ≤ (|x| + |y|) ^ i * (|x| + |y|) ^ (r - 1 - i) := by
              apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 _)
                (pow_le_pow_left₀ (abs_nonneg _) h2 _) (by positivity) (by positivity)
          _ = (|x| + |y|) ^ (r - 1) := by rw [← pow_add]; congr 1; omega
      _ = _ := by simp
  calc |y| * |∑ i ∈ Finset.range r, (x + y) ^ i * x ^ (r - 1 - i)|
      ≤ |y| * (r * (|x| + |y|) ^ (r - 1)) := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = _ := by ring
