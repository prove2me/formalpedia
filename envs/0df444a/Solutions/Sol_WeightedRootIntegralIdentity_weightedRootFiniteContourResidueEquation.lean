-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootFiniteContourResidueEquation
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-18T21:58:28.026382+00:00
-- url     : https://prove2.me/submissions/64ad608a-634a-4d74-8fde-b31fb7f2be1a

import Mathlib
import Definitions.Def_weightedRootFiniteContourComponentsV2
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (a₀ a₁ r R : ℝ) (residue : ℂ)
    (hdecomp : weightedRootBoundaryIntegral n a w a₀ a₁ r R =
      weightedRootFiniteUpperBankIntegral n a w a₀ a₁ r +
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ r +
      weightedRootRightVerticalIntegral n a w a₁ r R +
      weightedRootLeftVerticalIntegral n a w a₀ r R +
      weightedRootFiniteInnerArcIntegral n a w r +
      weightedRootFiniteOuterArcIntegral n a w R)
    (hres : weightedRootBoundaryIntegral n a w a₀ a₁ r R =
      2 * Real.pi * Complex.I * residue) :
    weightedRootFiniteUpperBankIntegral n a w a₀ a₁ r +
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ r +
      weightedRootRightVerticalIntegral n a w a₁ r R +
      weightedRootLeftVerticalIntegral n a w a₀ r R +
      weightedRootFiniteInnerArcIntegral n a w r +
      weightedRootFiniteOuterArcIntegral n a w R =
      2 * Real.pi * Complex.I * residue := by
  rw [← hdecomp]
  exact hres
