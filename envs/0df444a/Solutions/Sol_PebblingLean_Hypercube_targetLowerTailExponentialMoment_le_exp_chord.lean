-- Prove2me | solution 1 for PebblingLean.Hypercube.targetLowerTailExponentialMoment_le_exp_chord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:17.784483+00:00
-- url     : https://prove2.me/submissions/05ac5a7c-3764-4374-86fd-436a023abc73

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_oneCenterNegativeExponentialMoment_nonneg
public import Theorems.Thm_PebblingLean_Hypercube_oneCenterNegativeExponentialMoment_le_chord
public import Theorems.Thm_PebblingLean_Hypercube_targetLowerTailExponentialMoment_eq
public import Theorems.Thm_PebblingLean_FiniteProbability_pow_le_exp_neg_mul_of_le_one_sub
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
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n) {lam : ℝ}
    (hlam_nonneg : 0 ≤ lam) :
    targetLowerTailExponentialMoment (N := N) rIn rOut T target lam ≤
      Real.exp
        (lam * (T : ℝ) -
          (N : ℝ) *
            ((1 - Real.exp (-(lam * (2 ^ (rOut - rIn) : ℝ)))) *
              (oneCenterContributionExpectationReal rIn rOut target /
                (2 ^ (rOut - rIn) : ℝ)))) := by
  classical
  let B : ℝ := (2 ^ (rOut - rIn) : ℝ)
  let m : ℝ := oneCenterContributionExpectationReal rIn rOut target
  let u : ℝ := (1 - Real.exp (-(lam * B))) * (m / B)
  have hm_nonneg : 0 ≤ m := by
    unfold m oneCenterContributionExpectationReal uniformExpectationReal
    exact div_nonneg
      (Finset.sum_nonneg fun center _hcenter => by positivity)
      (by positivity)
  have hB_nonneg : 0 ≤ B := by positivity
  have hq_nonneg : 0 ≤ 1 - Real.exp (-(lam * B)) := by
    have harg : -(lam * B) ≤ 0 := by
      nlinarith [mul_nonneg hlam_nonneg hB_nonneg]
    simp_all
  have hmoment_chord :
      oneCenterNegativeExponentialMoment rIn rOut target lam ≤ 1 - u := by
    simpa [B, m, u] using
      oneCenterNegativeExponentialMoment_le_chord
        (rIn := rIn) (rOut := rOut) target lam
  have hpow :
      (oneCenterNegativeExponentialMoment rIn rOut target lam) ^ N ≤
        Real.exp (-((N : ℝ) * u)) := by
    exact pow_le_exp_neg_mul_of_le_one_sub N
      (oneCenterNegativeExponentialMoment_nonneg
        (rIn := rIn) (rOut := rOut) target lam)
      hmoment_chord
  rw [targetLowerTailExponentialMoment_eq]
  calc
    Real.exp (lam * (T : ℝ)) *
        (oneCenterNegativeExponentialMoment rIn rOut target lam) ^ N
        ≤ Real.exp (lam * (T : ℝ)) * Real.exp (-((N : ℝ) * u)) := by
          exact mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
    _ = Real.exp
        (lam * (T : ℝ) -
          (N : ℝ) *
            ((1 - Real.exp (-(lam * (2 ^ (rOut - rIn) : ℝ)))) *
              (oneCenterContributionExpectationReal rIn rOut target /
                (2 ^ (rOut - rIn) : ℝ)))) := by
          rw [← Real.exp_add]
          simp [B, m, u]
          ring
end PebblingLean.Hypercube
