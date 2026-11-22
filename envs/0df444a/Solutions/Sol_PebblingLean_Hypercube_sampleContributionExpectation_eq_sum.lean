-- Prove2me | solution 1 for PebblingLean.Hypercube.sampleContributionExpectation_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:25.428838+00:00
-- url     : https://prove2.me/submissions/0231d290-d502-4846-83e6-a3282e0dff02

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
theorem _root_.solution {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    sampleContributionExpectation (N := N) rIn rOut target =
      (∑ sample : CenterSample n N,
          (sampleTotalContribution rIn rOut target sample : ℚ)) /
        (Fintype.card (CenterSample n N) : ℚ) := by
  rfl
end PebblingLean.Hypercube
