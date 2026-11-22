-- Prove2me | solution 1 for PebblingLean.Hypercube.hasHighDemandDistribution_of_optimized_chord_annulusMean_log_of_mean_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:19.05421+00:00
-- url     : https://prove2.me/submissions/5c5008d7-7078-48f4-bf27-e68a53043fcc

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_globalFailureProbability_le_sum_targetFailureProbability
public import Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_of_globalFailureProbability_lt_one
public import Theorems.Thm_PebblingLean_Hypercube_bernsteinTargetFailureBound_of_optimized_chord_annulusMean
public import Theorems.Thm_PebblingLean_Hypercube_hypercube_card_mul_inv_two_pow_succ_lt_one
public import Theorems.Thm_PebblingLean_FiniteProbability_exp_neg_le_inv_two_pow_succ_of_log_le
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
    {n N rIn rOut T : ℕ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hlog :
      ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ)))) :
    HasHighDemandDistribution n T (N * 2 ^ rOut) (2 ^ rOut) := by
  have hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ) := by
    have hT_nonneg : 0 ≤ (T : ℝ) := by positivity
    nlinarith
  have hfailure :
      globalFailureProbability (n := n) (N := N) rIn rOut T < 1 := by
    have hbernstein :=
      bernsteinTargetFailureBound_of_optimized_chord_annulusMean
        (eps := (1 : ℚ) / (2 ^ (n + 1) : ℚ))
        hgap_pos hmu_pos hmean
        (by
          simpa using exp_neg_le_inv_two_pow_succ_of_log_le n hlog)
    have hglobal_le := globalFailureProbability_le_sum_targetFailureProbability
      (n := n) (N := N) (rIn := rIn) (rOut := rOut) (T := T)
    have hsum_le :
        (∑ target : HypercubeVertex n,
          targetFailureProbability (N := N) rIn rOut T target) ≤
          ∑ _target : HypercubeVertex n,
            ((1 : ℚ) / (2 ^ (n + 1) : ℚ)) := by
      exact Finset.sum_le_sum fun target _ => hbernstein target
    have hsum_eps :
        (∑ _target : HypercubeVertex n,
            ((1 : ℚ) / (2 ^ (n + 1) : ℚ))) =
          (Fintype.card (HypercubeVertex n) : ℚ) *
            ((1 : ℚ) / (2 ^ (n + 1) : ℚ)) := by
      simp
    exact lt_of_le_of_lt (hglobal_le.trans hsum_le)
      (by
        simpa [hsum_eps] using
          hypercube_card_mul_inv_two_pow_succ_lt_one n)
  exact hasHighDemandDistribution_of_globalFailureProbability_lt_one hfailure
end PebblingLean.Hypercube
