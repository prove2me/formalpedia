-- Prove2me | solution 1 for PebblingLean.Hypercube.chernoffExponentialMomentBound_of_oneCenterExponentialMomentBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:13.246119+00:00
-- url     : https://prove2.me/submissions/c05978ef-ba51-408e-bc93-185708600bf4

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_oneCenterNegativeExponentialMoment_eq_of_targets
public import Theorems.Thm_PebblingLean_Hypercube_targetLowerTailExponentialMoment_eq

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution
    {n N rIn rOut T : ℕ} {lam eps : ℝ}
    (hbound : OneCenterExponentialMomentBound n N rIn rOut T lam eps) :
    ChernoffExponentialMomentBound n N rIn rOut T eps := by
  intro target
  rcases hbound with ⟨hlam, hmoment⟩
  refine ⟨lam, hlam, ?_⟩
  rw [targetLowerTailExponentialMoment_eq]
  rw [oneCenterNegativeExponentialMoment_eq_of_targets
    target (fun _ : Fin n => false) lam]
  exact hmoment
end PebblingLean.Hypercube
