-- Prove2me | solution 1 for PebblingLean.Hypercube.oneCenterContributionExpectationReal_eq_annulusMean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:39.613991+00:00
-- url     : https://prove2.me/submissions/581e3edf-7129-4a2b-bc6e-d849dcfa59d7

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_oneCenterContributionExpectation_eq_annulusMean
public import Theorems.Thm_PebblingLean_Hypercube_oneCenterContributionExpectationReal_eq_coe

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
    oneCenterContributionExpectationReal rIn rOut target =
      (annulusMean n rIn rOut : ℝ) := by
  rw [oneCenterContributionExpectationReal_eq_coe]
  rw [oneCenterContributionExpectation_eq_annulusMean]
end PebblingLean.Hypercube
