-- Prove2me | solution 1 for PebblingLean.Hypercube.exists_goodCenterSample_of_oneCenterDistanceSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:39.549149+00:00
-- url     : https://prove2.me/submissions/f03e8eed-0ba9-42e8-a062-e54df588a797

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_bernsteinExponentialMomentBound_of_oneCenterDistanceSum
public import Theorems.Thm_PebblingLean_Hypercube_exists_goodCenterSample_of_bernsteinExponentialMomentBound

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution
    {n N rIn rOut T : ℕ} {lam variance scale gap : ℝ} {eps : ℚ}
    (hbound :
      OneCenterDistanceSumExponentialMomentBound n N rIn rOut T lam
        (Real.exp (-(bernsteinExponent variance scale gap))))
    (hexp : Real.exp (-(bernsteinExponent variance scale gap)) ≤ (eps : ℝ))
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList :=
  exists_goodCenterSample_of_bernsteinExponentialMomentBound
    (bernsteinExponentialMomentBound_of_oneCenterDistanceSum hbound) hexp hunion
end PebblingLean.Hypercube
