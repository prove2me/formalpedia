-- Prove2me | solution 1 for bernoulli_sampled_row_count_max_moment_from_large_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:40.513302+00:00
-- url     : https://prove2.me/submissions/dbf86c26-fe77-40f9-845f-bbe77bc257e8

import Theorems.Thm_bernoulli_nonnegative_statistic_moment_from_scaled_large_deviation_bound
import Theorems.Thm_sampled_row_count_max_nonnegative

open MatrixCompletion

/-- Specialize the generic nonnegative-statistic tail-to-moment estimate to
the maximum sampled row count. -/
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
                  sampledRowCountMax Omega) ≤
            (↑(max n₁ n₂)) *
              Real.exp
                (-(lambda *
                    (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (↑(max n₁ n₂)))) / Cdev)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega : Finset (Fin n₁ × Fin n₂) =>
              sampledRowCountMax Omega ^ q) ≤
          (Ccount * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂))) ^ q := by
  intro hCdev
  rcases bernoulli_nonnegative_statistic_moment_from_scaled_large_deviation_bound
      Cdev hCdev with
    ⟨Ccount, hCcount, hMoment⟩
  refine ⟨Ccount, hCcount, ?_⟩
  intro β hβ n₁ n₂ m q hn₁ hn₂ hm hqOne hqLog hqUpper hTail
  exact hMoment β hβ n₁ n₂ m q hn₁ hn₂ hm hqOne hqLog hqUpper
    (fun Omega => sampledRowCountMax Omega)
    (fun Omega => sampled_row_count_max_nonnegative Omega)
    hTail
