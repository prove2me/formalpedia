-- Prove2me | solution 1 for PebblingLean.Hypercube.oneCenterNegativeExponentialMoment_eq_of_targets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:23.067875+00:00
-- url     : https://prove2.me/submissions/18c7654d-c8e7-45c6-8da3-c0225e287316

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_oneCenterNegativeExponentialMoment_eq_distance_sum

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution {n rIn rOut : ℕ}
    (target target' : HypercubeVertex n) (lam : ℝ) :
    oneCenterNegativeExponentialMoment rIn rOut target lam =
      oneCenterNegativeExponentialMoment rIn rOut target' lam := by
  rw [oneCenterNegativeExponentialMoment_eq_distance_sum target lam,
    oneCenterNegativeExponentialMoment_eq_distance_sum target' lam]
end PebblingLean.Hypercube
