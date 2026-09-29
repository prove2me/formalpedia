-- Prove2me | solution 1 for bernoulli_uniform_coordinate_bound_from_pointwise_tails_with_cardinality_factor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T19:51:21.435212+00:00
-- url     : https://prove2.me/submissions/a6fd17b2-5c00-4be0-b508-7f584907057e

import Theorems.Thm_bernoulli_finite_coordinate_intersection_probability_from_pointwise_bounds

open MatrixCompletion

theorem solution
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∀ (p scale failureScale : ℝ), 0 ≤ p → p ≤ 1 →
      ∀ (n₁ n₂ : ℕ),
        ∀ Coeff : (Fin n₁ × Fin n₂) →
          Finset (Fin n₁ × Fin n₂) → ℝ,
        (∀ w : Fin n₁ × Fin n₂,
          bernoulliEventProb p
              (fun Omega => |Coeff w Omega| ≤ Cpoint * scale) ≥
            1 - cpoint * failureScale) →
        bernoulliEventProb p
            (fun Omega =>
              ∀ w : Fin n₁ × Fin n₂,
                |Coeff w Omega| ≤ Cpoint * scale) ≥
          1 - (((Fintype.card (Fin n₁ × Fin n₂) : ℝ) * cpoint) *
            failureScale) := by
  intro _hCpoint _hcpoint p scale failureScale hp hp_one n₁ n₂ Coeff hPoint
  exact
    bernoulli_finite_coordinate_intersection_probability_from_pointwise_bounds
      p cpoint failureScale
      (fun w Omega => |Coeff w Omega| ≤ Cpoint * scale)
      hp hp_one hPoint
