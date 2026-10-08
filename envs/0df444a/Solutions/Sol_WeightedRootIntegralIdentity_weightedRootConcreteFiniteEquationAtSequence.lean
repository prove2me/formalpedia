-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootConcreteFiniteEquationAtSequence
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T08:33:41.195223+00:00
-- url     : https://prove2.me/submissions/6e8ad6af-63a3-4f79-80dc-4ef2286cdb34

import Mathlib
import Definitions.Def_weightedRootFiniteContourComponentsV2
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (a₀ a₁ : ℝ) (ρ : ℂ)
    (hdecomp : ∀ m : ℕ,
      weightedRootBoundaryIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) =
        weightedRootFiniteUpperBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) +
        weightedRootFiniteLowerBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) +
        weightedRootRightVerticalIntegral n a w a₁ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) +
        weightedRootLeftVerticalIntegral n a w a₀ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) +
        weightedRootFiniteInnerArcIntegral n a w (1 / (m + 1 : ℝ)) +
        weightedRootFiniteOuterArcIntegral n a w (m + 1 : ℝ))
    (hres : ∀ m : ℕ,
      weightedRootBoundaryIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) = ρ) :
    ∀ m : ℕ,
      weightedRootFiniteUpperBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) +
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) +
      weightedRootRightVerticalIntegral n a w a₁ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) +
      weightedRootLeftVerticalIntegral n a w a₀ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) +
      weightedRootFiniteInnerArcIntegral n a w (1 / (m + 1 : ℝ)) +
      weightedRootFiniteOuterArcIntegral n a w (m + 1 : ℝ) = ρ := by
  intro m
  rw [← hdecomp m]
  exact hres m
