-- Prove2me | solution 1 for PebblingLean.Hypercube.globalFailureProbability_le_sum_targetFailureProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:24.651858+00:00
-- url     : https://prove2.me/submissions/107a9f39-8673-46e1-aef6-b1f9b5c17143

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_FiniteProbability_uniformProbability_exists_le_sum


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution {n N rIn rOut T : ℕ} :
    globalFailureProbability (n := n) (N := N) rIn rOut T ≤
      ∑ target : HypercubeVertex n,
        targetFailureProbability (N := N) rIn rOut T target := by
  classical
  change
    uniformProbability
        (fun sample : CenterSample n N =>
          ∃ target : HypercubeVertex n,
            sampleTotalContribution rIn rOut target sample < T) ≤
      ∑ target : HypercubeVertex n,
        uniformProbability
          (fun sample : CenterSample n N =>
            sampleTotalContribution rIn rOut target sample < T)
  exact
      (uniformProbability_exists_le_sum
        (Ω := CenterSample n N) (ι := HypercubeVertex n)
        (fun target sample => sampleTotalContribution rIn rOut target sample < T))
end PebblingLean.Hypercube
