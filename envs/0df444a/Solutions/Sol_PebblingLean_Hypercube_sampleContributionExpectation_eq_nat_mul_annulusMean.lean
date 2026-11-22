-- Prove2me | solution 1 for PebblingLean.Hypercube.sampleContributionExpectation_eq_nat_mul_annulusMean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:42.71533+00:00
-- url     : https://prove2.me/submissions/036b3b0a-ef87-45cb-9689-e16061ce137f

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_oneCenterContributionExpectation_eq_annulusMean
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
    sampleContributionExpectation (N := N) rIn rOut target =
      (N : ℚ) * annulusMean n rIn rOut := by
  rw [sampleContributionExpectation_eq_nat_mul_oneCenter]
  rw [oneCenterContributionExpectation_eq_annulusMean]
end PebblingLean.Hypercube
