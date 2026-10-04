-- Prove2me | solution 2 for TaoFivePrimes.vinogradov_lemma_if_form
-- status  : ACCEPTED   (disprove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T02:21:55.664112+00:00
-- url     : https://prove2.me/submissions/64ba2480-70e1-48dc-a577-c911ac0e6bdb

import Mathlib

open Finset

/-- The negation of the whole quantified statement. -/
theorem solution : ¬ (∀ (B : ℝ), 0 ≤ B → ∀ (q : ℕ), 0 < q →
    ∀ (A' alpha' beta' theta' u v : ℝ), ∀ (a' : ℤ),
    0 ≤ A' → alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
    (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
          * (2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q))) := by
  intro h
  have hh := h (0 : ℝ) (by norm_num) 10 (by norm_num)
      (1 : ℝ) (0 : ℝ) (0 : ℝ) (0 : ℝ) (0 : ℝ) (10 : ℝ) (0 : ℤ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hh
