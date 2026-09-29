-- Prove2me | solution 1 for bernoulli_sampled_row_count_max_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:40.083115+00:00
-- url     : https://prove2.me/submissions/b69b3244-f067-43e4-9851-0e804dd76b28

import Theorems.Thm_bernoulli_sampled_row_count_max_large_deviation_bound
import Theorems.Thm_bernoulli_sampled_row_count_max_moment_from_large_deviation_bound

open MatrixCompletion

/-- Appendix 9.2 row-count moment reduction: combine the maximum-count
large-deviation bound with the tail-to-moment calculation. -/
theorem solution :
    ∃ Ccount : ℝ, 0 < Ccount ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega : Finset (Fin n₁ × Fin n₂) =>
              sampledRowCountMax Omega ^ q) ≤
          (Ccount * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂))) ^ q := by
  rcases bernoulli_sampled_row_count_max_large_deviation_bound with
    ⟨Cdev, hCdev, hTail⟩
  rcases bernoulli_sampled_row_count_max_moment_from_large_deviation_bound
      Cdev hCdev with
    ⟨Ccount, hCcount, hMoment⟩
  refine ⟨Ccount, hCcount, ?_⟩
  intro β hβ n₁ n₂ m q hn₁ hn₂ hm hqOne hqLog hqUpper
  exact hMoment β hβ n₁ n₂ m q hn₁ hn₂ hm hqOne hqLog hqUpper
    (hTail n₁ n₂ m hn₁ hn₂ hm)
