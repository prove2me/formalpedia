-- Prove2me | solution 1 for PebblingLean.Hypercube.bernsteinTargetFailureBound_of_chernoffExponentialMomentBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:06:54.409998+00:00
-- url     : https://prove2.me/submissions/68e895f5-5fbd-452c-b397-31cbb711ba18

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_targetFailureProbability_le_of_exponentialMoment_le

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution
    {n N rIn rOut T : ℕ} {epsReal : ℝ} {eps : ℚ}
    (hmoment : ChernoffExponentialMomentBound n N rIn rOut T epsReal)
    (heps : epsReal ≤ (eps : ℝ)) :
    BernsteinTargetFailureBound n N rIn rOut T eps := by
  intro target
  rcases hmoment target with ⟨lam, hlam, hmoment_target⟩
  exact targetFailureProbability_le_of_exponentialMoment_le target hlam
    (hmoment_target.trans heps)
end PebblingLean.Hypercube
