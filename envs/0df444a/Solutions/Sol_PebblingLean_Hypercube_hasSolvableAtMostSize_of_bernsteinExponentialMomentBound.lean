-- Prove2me | solution 1 for PebblingLean.Hypercube.hasSolvableAtMostSize_of_bernsteinExponentialMomentBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:03.731485+00:00
-- url     : https://prove2.me/submissions/3ef46399-145b-48bd-a850-429cc31d26df

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_bernsteinTargetFailureBound_of_bernsteinExponentialMomentBound
public import Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_of_bernstein_bound

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
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) :=
  hasSolvableAtMostSize_of_bernstein_bound
    (bernsteinTargetFailureBound_of_bernsteinExponentialMomentBound hmoment hexp) hunion
end PebblingLean.Hypercube
