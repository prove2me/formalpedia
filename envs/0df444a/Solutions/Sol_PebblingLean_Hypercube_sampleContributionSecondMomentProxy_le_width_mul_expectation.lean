-- Prove2me | solution 1 for PebblingLean.Hypercube.sampleContributionSecondMomentProxy_le_width_mul_expectation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:10.875559+00:00
-- url     : https://prove2.me/submissions/7606c77c-9d0d-483a-9f5e-7142a86b66c7

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_oneCenterContributionSecondMoment_le_width_mul_expectation
public import Theorems.Thm_PebblingLean_Hypercube_sampleContributionExpectation_eq_nat_mul_oneCenter

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    sampleContributionSecondMomentProxy (N := N) rIn rOut target ≤
      (2 ^ (rOut - rIn) : ℚ) *
        sampleContributionExpectation (N := N) rIn rOut target := by
  rw [sampleContributionSecondMomentProxy,
    sampleContributionExpectation_eq_nat_mul_oneCenter]
  have hN : 0 ≤ (N : ℚ) := by positivity
  have h :=
    mul_le_mul_of_nonneg_left
      (oneCenterContributionSecondMoment_le_width_mul_expectation
        (rIn := rIn) (rOut := rOut) target) hN
  calc
    (N : ℚ) * oneCenterContributionSecondMoment rIn rOut target
        ≤ (N : ℚ) *
          ((2 ^ (rOut - rIn) : ℚ) * oneCenterContributionExpectation rIn rOut target) := h
    _ = (2 ^ (rOut - rIn) : ℚ) *
        ((N : ℚ) * oneCenterContributionExpectation rIn rOut target) := by
          ring
end PebblingLean.Hypercube
