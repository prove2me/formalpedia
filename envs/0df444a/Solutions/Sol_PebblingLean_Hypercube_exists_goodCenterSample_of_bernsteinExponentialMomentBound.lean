-- Prove2me | solution 1 for PebblingLean.Hypercube.exists_goodCenterSample_of_bernsteinExponentialMomentBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:36.337008+00:00
-- url     : https://prove2.me/submissions/2157b1fe-cbc8-4fa8-b3b2-a2d19d710486

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_bernsteinTargetFailureBound_of_bernsteinExponentialMomentBound
public import Theorems.Thm_PebblingLean_Hypercube_exists_goodCenterSample_of_bernstein_bound

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution
    {n N rIn rOut T : ℕ} {variance scale gap : ℝ} {eps : ℚ}
    (hmoment : BernsteinExponentialMomentBound n N rIn rOut T variance scale gap)
    (hexp : Real.exp (-(bernsteinExponent variance scale gap)) ≤ (eps : ℝ))
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList :=
  exists_goodCenterSample_of_bernstein_bound
    (bernsteinTargetFailureBound_of_bernsteinExponentialMomentBound hmoment hexp) hunion
end PebblingLean.Hypercube
