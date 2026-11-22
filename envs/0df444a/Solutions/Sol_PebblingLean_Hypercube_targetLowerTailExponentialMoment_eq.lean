-- Prove2me | solution 1 for PebblingLean.Hypercube.targetLowerTailExponentialMoment_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:06:30.311801+00:00
-- url     : https://prove2.me/submissions/f4f4bec4-e177-4a50-b92d-6c0abf20dbdc

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_sum_exp_neg_sampleTotalContribution_eq_pow
public import Theorems.Thm_PebblingLean_Hypercube_exp_target_sub_sampleTotalContribution
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
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n) (lam : ℝ) :
    targetLowerTailExponentialMoment (N := N) rIn rOut T target lam =
      Real.exp (lam * (T : ℝ)) *
        (oneCenterNegativeExponentialMoment rIn rOut target lam) ^ N := by
  classical
  let A : ℝ :=
    ∑ center : HypercubeVertex n,
      Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))
  have hsum :
      (∑ sample : CenterSample n N,
        Real.exp (lam * ((T : ℝ) -
          (sampleTotalContribution rIn rOut target sample : ℝ)))) =
        Real.exp (lam * (T : ℝ)) * A ^ N := by
    calc
      (∑ sample : CenterSample n N,
        Real.exp (lam * ((T : ℝ) -
          (sampleTotalContribution rIn rOut target sample : ℝ))))
          = ∑ sample : CenterSample n N,
            Real.exp (lam * (T : ℝ)) *
              Real.exp (-(lam *
                (sampleTotalContribution rIn rOut target sample : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro sample _hsample
            exact exp_target_sub_sampleTotalContribution target lam sample
      _ = Real.exp (lam * (T : ℝ)) *
          ∑ sample : CenterSample n N,
            Real.exp (-(lam *
              (sampleTotalContribution rIn rOut target sample : ℝ))) := by
            rw [Finset.mul_sum]
      _ = Real.exp (lam * (T : ℝ)) * A ^ N := by
            rw [sum_exp_neg_sampleTotalContribution_eq_pow]
  have hcard_ne : (2 ^ n : ℝ) ≠ 0 := by
    positivity
  have hcard_pow_ne : ((2 ^ n : ℝ) ^ N) ≠ 0 := pow_ne_zero N hcard_ne
  simp [targetLowerTailExponentialMoment, oneCenterNegativeExponentialMoment,
    uniformExpectationReal, A, hsum, Nat.cast_pow]
  field_simp [hcard_ne, hcard_pow_ne]
  rw [div_pow]
  field_simp [hcard_pow_ne]
end PebblingLean.Hypercube
