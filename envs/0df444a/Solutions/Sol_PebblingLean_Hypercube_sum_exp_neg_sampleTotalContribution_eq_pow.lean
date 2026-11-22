-- Prove2me | solution 1 for PebblingLean.Hypercube.sum_exp_neg_sampleTotalContribution_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:05:42.510256+00:00
-- url     : https://prove2.me/submissions/50916380-27b6-460f-9f51-adb4256d5c94

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_exp_neg_sampleTotalContribution_eq_prod
public import Theorems.Thm_PebblingLean_Hypercube_sum_prod_oneCenterNegativeExponentialMoment

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    (∑ sample : CenterSample n N,
      Real.exp (-(lam * (sampleTotalContribution rIn rOut target sample : ℝ)))) =
      (∑ center : HypercubeVertex n,
        Real.exp (-(lam *
          (annulusContribution rIn rOut target center : ℝ)))) ^ N := by
  classical
  calc
    (∑ sample : CenterSample n N,
      Real.exp (-(lam * (sampleTotalContribution rIn rOut target sample : ℝ))))
        = ∑ sample : CenterSample n N,
          ∏ j : Fin N,
            Real.exp (-(lam *
              (annulusContribution rIn rOut target (sample j) : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro sample _hsample
          exact exp_neg_sampleTotalContribution_eq_prod target lam sample
    _ = (∑ center : HypercubeVertex n,
        Real.exp (-(lam *
          (annulusContribution rIn rOut target center : ℝ)))) ^ N := by
          exact sum_prod_oneCenterNegativeExponentialMoment target lam
end PebblingLean.Hypercube
