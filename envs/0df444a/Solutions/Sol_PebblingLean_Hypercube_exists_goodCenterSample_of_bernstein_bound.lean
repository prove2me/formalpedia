-- Prove2me | solution 1 for PebblingLean.Hypercube.exists_goodCenterSample_of_bernstein_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:05:41.349713+00:00
-- url     : https://prove2.me/submissions/df98ac4e-bc61-4e07-87a3-c0c76463d79c

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_globalFailureProbability_le_sum_targetFailureProbability
public import Theorems.Thm_PebblingLean_Hypercube_exists_goodCenterSample_of_globalFailureProbability_lt_one
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
theorem _root_.solution {n N rIn rOut T : ℕ} {eps : ℚ}
    (hbernstein : BernsteinTargetFailureBound n N rIn rOut T eps)
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList := by
  classical
  have hglobal_le := globalFailureProbability_le_sum_targetFailureProbability
    (n := n) (N := N) (rIn := rIn) (rOut := rOut) (T := T)
  have hsum_le :
      (∑ target : HypercubeVertex n,
        targetFailureProbability (N := N) rIn rOut T target) ≤
        ∑ _target : HypercubeVertex n, eps := by
    exact Finset.sum_le_sum fun target _ => hbernstein target
  have hsum_eps :
      (∑ _target : HypercubeVertex n, eps) =
        (Fintype.card (HypercubeVertex n) : ℚ) * eps := by
    simp
  have hprob :
      globalFailureProbability (n := n) (N := N) rIn rOut T < 1 := by
    exact lt_of_le_of_lt (hglobal_le.trans hsum_le) (by simpa [hsum_eps] using hunion)
  exact exists_goodCenterSample_of_globalFailureProbability_lt_one hprob
end PebblingLean.Hypercube
