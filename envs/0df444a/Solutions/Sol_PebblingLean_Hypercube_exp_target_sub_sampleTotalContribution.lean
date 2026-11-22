-- Prove2me | solution 1 for PebblingLean.Hypercube.exp_target_sub_sampleTotalContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:31.323599+00:00
-- url     : https://prove2.me/submissions/ca4d5277-9ba4-48be-8368-f6d89337f335

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n)
    (lam : ℝ) (sample : CenterSample n N) :
    Real.exp (lam * ((T : ℝ) -
        (sampleTotalContribution rIn rOut target sample : ℝ))) =
      Real.exp (lam * (T : ℝ)) *
        Real.exp (-(lam *
          (sampleTotalContribution rIn rOut target sample : ℝ))) := by
  have harg :
      lam * ((T : ℝ) -
          (sampleTotalContribution rIn rOut target sample : ℝ)) =
        lam * (T : ℝ) +
          -(lam * (sampleTotalContribution rIn rOut target sample : ℝ)) := by
    ring
  rw [harg, Real.exp_add]
end PebblingLean.Hypercube
