-- Prove2me | solution 1 for PebblingLean.Hypercube.targetFailureProbability_le_exp_neg_of_exponentialMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:14.310244+00:00
-- url     : https://prove2.me/submissions/877abdb0-0a08-44cd-b669-aa4054d38bfb

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
theorem _root_.solution {n N rIn rOut T : ℕ}
    (target : HypercubeVertex n) {lam exponent : ℝ} {eps : ℚ}
    (hlam : 0 < lam)
    (hmoment :
      targetLowerTailExponentialMoment (N := N) rIn rOut T target lam ≤
        Real.exp (-exponent))
    (hexp : Real.exp (-exponent) ≤ (eps : ℝ)) :
    targetFailureProbability (N := N) rIn rOut T target ≤ eps :=
  targetFailureProbability_le_of_exponentialMoment_le target hlam (hmoment.trans hexp)
end PebblingLean.Hypercube
