-- Prove2me | solution 1 for bernoulli_sampled_column_count_max_moment_from_large_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:38.289575+00:00
-- url     : https://prove2.me/submissions/d1ea6b8d-7d23-4f8f-a612-691fa3b367bc

import Theorems.Thm_bernoulli_nonnegative_statistic_moment_from_scaled_large_deviation_bound
import Theorems.Thm_sampled_column_count_max_nonnegative

open MatrixCompletion

/-- Specialize the generic nonnegative-statistic tail-to-moment estimate to
the maximum sampled column count. -/
theorem solution
    (Cdev : ℝ) :
    0 < Cdev →
    ∃ Ccount : ℝ, 0 < Ccount ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂)) →
        (∀ lambda : ℝ, 2 ≤ lambda →
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega : Finset (Fin n₁ × Fin n₂) =>
                lambda *
                    (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (↑(max n₁ n₂))) <
                  sampledColumnCountMax Omega) ≤
            (↑(max n₁ n₂)) *
              Real.exp
                (-(lambda *
                    (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (↑(max n₁ n₂)))) / Cdev)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega : Finset (Fin n₁ × Fin n₂) =>
              sampledColumnCountMax Omega ^ q) ≤
          (Ccount * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂))) ^ q := by
  intro hCdev
  rcases bernoulli_nonnegative_statistic_moment_from_scaled_large_deviation_bound
      Cdev hCdev with
    ⟨Ccount, hCcount, hMoment⟩
  refine ⟨Ccount, hCcount, ?_⟩
  intro β hβ n₁ n₂ m q hn₁ hn₂ hm hqOne hqLog hqUpper hTail
  exact hMoment β hβ n₁ n₂ m q hn₁ hn₂ hm hqOne hqLog hqUpper
    (fun Omega => sampledColumnCountMax Omega)
    (fun Omega => sampled_column_count_max_nonnegative Omega)
    hTail
