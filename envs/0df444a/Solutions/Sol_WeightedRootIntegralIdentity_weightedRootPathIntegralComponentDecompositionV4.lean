-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootPathIntegralComponentDecompositionV4
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T04:53:58.801167+00:00
-- url     : https://prove2.me/submissions/4f0ddea5-be40-4ac2-b345-85fca1c28c59

import Mathlib
import Definitions.Def_weightedRootFiniteContourComponentsV2
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (a₀ a₁ r R : ℝ) (P : ℂ)
    (hpath : P = weightedRootBoundaryIntegral n a w a₀ a₁ r R)
    (hdecomp : weightedRootBoundaryIntegral n a w a₀ a₁ r R =
      weightedRootFiniteUpperBankIntegral n a w a₀ a₁ r +
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ r +
      weightedRootRightVerticalIntegral n a w a₁ r R +
      weightedRootLeftVerticalIntegral n a w a₀ r R +
      weightedRootFiniteInnerArcIntegral n a w r +
      weightedRootFiniteOuterArcIntegral n a w R) :
    P = weightedRootFiniteUpperBankIntegral n a w a₀ a₁ r +
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ r +
      weightedRootRightVerticalIntegral n a w a₁ r R +
      weightedRootLeftVerticalIntegral n a w a₀ r R +
      weightedRootFiniteInnerArcIntegral n a w r +
      weightedRootFiniteOuterArcIntegral n a w R := by
  rw [hpath, hdecomp]
