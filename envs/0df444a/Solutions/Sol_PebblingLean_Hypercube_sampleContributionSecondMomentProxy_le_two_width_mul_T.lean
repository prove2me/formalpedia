-- Prove2me | solution 1 for PebblingLean.Hypercube.sampleContributionSecondMomentProxy_le_two_width_mul_T
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:12.309838+00:00
-- url     : https://prove2.me/submissions/b3d856de-7400-40aa-af90-8cc933303c52

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_sampleContributionSecondMomentProxy_le_width_mul_expectation

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n)
    (hmean_upper :
      sampleContributionExpectation (N := N) rIn rOut target ≤ 2 * (T : ℚ)) :
    sampleContributionSecondMomentProxy (N := N) rIn rOut target ≤
      2 * (2 ^ (rOut - rIn) : ℚ) * (T : ℚ) := by
  have hwidth_nonneg : 0 ≤ (2 ^ (rOut - rIn) : ℚ) := by positivity
  have h :=
    (sampleContributionSecondMomentProxy_le_width_mul_expectation
      (N := N) (rIn := rIn) (rOut := rOut) target).trans
      (mul_le_mul_of_nonneg_left hmean_upper hwidth_nonneg)
  calc
    sampleContributionSecondMomentProxy (N := N) rIn rOut target
        ≤ (2 ^ (rOut - rIn) : ℚ) * (2 * (T : ℚ)) := h
    _ = 2 * (2 ^ (rOut - rIn) : ℚ) * (T : ℚ) := by
          ring
end PebblingLean.Hypercube
