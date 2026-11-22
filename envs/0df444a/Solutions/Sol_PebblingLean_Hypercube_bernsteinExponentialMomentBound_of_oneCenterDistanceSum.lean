-- Prove2me | solution 1 for PebblingLean.Hypercube.bernsteinExponentialMomentBound_of_oneCenterDistanceSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:01.427339+00:00
-- url     : https://prove2.me/submissions/66edc041-f152-4974-ab03-da066813ddd0

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_oneCenterExponentialMomentBound_of_distanceSum
public import Theorems.Thm_PebblingLean_Hypercube_chernoffExponentialMomentBound_of_oneCenterExponentialMomentBound

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution
    {n N rIn rOut T : ℕ} {lam variance scale gap : ℝ}
    (hbound :
      OneCenterDistanceSumExponentialMomentBound n N rIn rOut T lam
        (Real.exp (-(bernsteinExponent variance scale gap)))) :
    BernsteinExponentialMomentBound n N rIn rOut T variance scale gap :=
  chernoffExponentialMomentBound_of_oneCenterExponentialMomentBound
    (oneCenterExponentialMomentBound_of_distanceSum hbound)
end PebblingLean.Hypercube
