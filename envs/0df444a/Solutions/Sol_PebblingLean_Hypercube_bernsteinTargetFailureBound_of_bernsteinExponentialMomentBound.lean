-- Prove2me | solution 1 for PebblingLean.Hypercube.bernsteinTargetFailureBound_of_bernsteinExponentialMomentBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:45.927846+00:00
-- url     : https://prove2.me/submissions/f627aca1-964a-4ee3-8e08-09c400655e29

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_bernsteinTargetFailureBound_of_chernoffExponentialMomentBound

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
    (hexp : Real.exp (-(bernsteinExponent variance scale gap)) ≤ (eps : ℝ)) :
    BernsteinTargetFailureBound n N rIn rOut T eps :=
  bernsteinTargetFailureBound_of_chernoffExponentialMomentBound hmoment hexp
end PebblingLean.Hypercube
