-- Prove2me | solution 1 for PebblingLean.Hypercube.sum_sampleTotalContribution_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:05:14.59818+00:00
-- url     : https://prove2.me/submissions/39f15119-2ee0-44dd-9005-8a3ba448a0e2

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_sum_centerSample_eval
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
theorem _root_.solution {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    (∑ sample : CenterSample n N,
        (sampleTotalContribution rIn rOut target sample : ℚ)) =
      (N : ℚ) * ((2 ^ n) ^ (N - 1) : ℚ) *
        ∑ center : HypercubeVertex n,
          (annulusContribution rIn rOut target center : ℚ) := by
  classical
  calc
    (∑ sample : CenterSample n N,
        (sampleTotalContribution rIn rOut target sample : ℚ))
        = ∑ sample : CenterSample n N,
            ∑ j : Fin N,
              (annulusContribution rIn rOut target (sample j) : ℚ) := by
          refine Finset.sum_congr rfl ?_
          intro sample _hsample
          simp [sampleTotalContribution]
    _ = ∑ j : Fin N,
        ∑ sample : CenterSample n N,
          (annulusContribution rIn rOut target (sample j) : ℚ) := by
          rw [Finset.sum_comm]
    _ = ∑ _j : Fin N,
        ((2 ^ n) ^ (N - 1) : ℚ) *
          ∑ center : HypercubeVertex n,
            (annulusContribution rIn rOut target center : ℚ) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          exact sum_centerSample_eval j (annulusContribution rIn rOut target)
    _ = (N : ℚ) * ((2 ^ n) ^ (N - 1) : ℚ) *
        ∑ center : HypercubeVertex n,
          (annulusContribution rIn rOut target center : ℚ) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
end PebblingLean.Hypercube
