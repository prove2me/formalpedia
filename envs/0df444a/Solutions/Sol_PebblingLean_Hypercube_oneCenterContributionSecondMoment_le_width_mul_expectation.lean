-- Prove2me | solution 1 for PebblingLean.Hypercube.oneCenterContributionSecondMoment_le_width_mul_expectation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:05:06.149825+00:00
-- url     : https://prove2.me/submissions/9e1dcede-3aa6-46c9-a57b-3ec951ae7207

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_oneCenterContributionExpectation_eq_sum
public import Theorems.Thm_PebblingLean_Hypercube_oneCenterContributionSecondMoment_eq_sum
public import Theorems.Thm_PebblingLean_Hypercube_annulusContribution_sq_le_width_mul


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    oneCenterContributionSecondMoment rIn rOut target ≤
      (2 ^ (rOut - rIn) : ℚ) * oneCenterContributionExpectation rIn rOut target := by
  classical
  rw [oneCenterContributionSecondMoment_eq_sum, oneCenterContributionExpectation_eq_sum]
  have hden_pos : 0 < (2 ^ n : ℚ) := by positivity
  have hsum :
      (∑ center : HypercubeVertex n,
          ((annulusContribution rIn rOut target center) ^ 2 : ℚ)) ≤
        (2 ^ (rOut - rIn) : ℚ) *
          ∑ center : HypercubeVertex n,
            (annulusContribution rIn rOut target center : ℚ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun center _hcenter => by
      exact_mod_cast
        annulusContribution_sq_le_width_mul
          (rIn := rIn) (rOut := rOut) target center
  calc
    (∑ center : HypercubeVertex n,
        ((annulusContribution rIn rOut target center) ^ 2 : ℚ)) / (2 ^ n : ℚ)
        ≤ ((2 ^ (rOut - rIn) : ℚ) *
          ∑ center : HypercubeVertex n,
            (annulusContribution rIn rOut target center : ℚ)) / (2 ^ n : ℚ) := by
          exact div_le_div_of_nonneg_right hsum hden_pos.le
    _ = (2 ^ (rOut - rIn) : ℚ) *
        ((∑ center : HypercubeVertex n,
            (annulusContribution rIn rOut target center : ℚ)) / (2 ^ n : ℚ)) := by
          ring
end PebblingLean.Hypercube
