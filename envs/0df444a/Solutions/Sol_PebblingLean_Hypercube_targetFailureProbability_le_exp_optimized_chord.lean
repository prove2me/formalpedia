-- Prove2me | solution 1 for PebblingLean.Hypercube.targetFailureProbability_le_exp_optimized_chord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:56.889097+00:00
-- url     : https://prove2.me/submissions/a633289d-b6bd-4f73-b779-8359340c86cb

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_targetLowerTailExponentialMoment_le_exp_optimized_chord
public import Theorems.Thm_PebblingLean_Hypercube_targetFailureProbability_le_of_exponentialMoment_le
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Hypercube_fromDiffSet_empty
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_self
public import Theorems.Thm_PebblingLean_Pebbling_size_single
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_left
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_right
attribute [local simp] PebblingLean.Graph.Walk.length_append
attribute [local simp] PebblingLean.Graph.Walk.length_reverse
attribute [local simp] PebblingLean.Hypercube.fromDiffSet_empty
attribute [local simp] PebblingLean.Hypercube.mem_annulus
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.single_apply_ne
attribute [local simp] PebblingLean.Pebbling.single_apply_self
attribute [local simp] PebblingLean.Pebbling.size_single
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_left
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_ne
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_right



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n) {gap : ℝ} {eps : ℚ}
    (hgap_pos : 0 < gap)
    (hmu_pos :
      0 < (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)
    (hmean :
      (T : ℝ) + gap ≤
        (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)
    (hexp :
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)))) ≤
        (eps : ℝ)) :
    targetFailureProbability (N := N) rIn rOut T target ≤ eps := by
  let mu : ℝ := (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target
  let B : ℝ := (2 ^ (rOut - rIn) : ℝ)
  let lam : ℝ := gap / (2 * B * mu)
  have hmu_pos' : 0 < mu := by simpa [mu] using hmu_pos
  have hlam_pos : 0 < lam := by
    have hden_pos : 0 < 2 * B * mu := by
      have hB_pos : 0 < B := by positivity
      positivity
    exact div_pos hgap_pos hden_pos
  have hmoment :=
    targetLowerTailExponentialMoment_le_exp_optimized_chord
      (N := N) (rIn := rIn) (rOut := rOut) (T := T)
      target (gap := gap) hgap_pos.le hmu_pos hmean
  have hmoment' :
      targetLowerTailExponentialMoment (N := N) rIn rOut T target lam ≤
        Real.exp
          (-(gap ^ 2 /
            (4 * (2 ^ (rOut - rIn) : ℝ) *
              ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)))) := by
    simpa [lam, B, mu] using hmoment
  exact targetFailureProbability_le_of_exponentialMoment_le
    target hlam_pos (hmoment'.trans hexp)
end PebblingLean.Hypercube
