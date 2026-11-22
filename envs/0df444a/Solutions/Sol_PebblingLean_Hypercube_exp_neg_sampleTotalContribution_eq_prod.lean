-- Prove2me | solution 1 for PebblingLean.Hypercube.exp_neg_sampleTotalContribution_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:04:29.883544+00:00
-- url     : https://prove2.me/submissions/9c4c25e1-ca06-4e3b-a0ff-2618fa04d139

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
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
    (target : HypercubeVertex n) (lam : ℝ) (sample : CenterSample n N) :
    Real.exp (-(lam * (sampleTotalContribution rIn rOut target sample : ℝ))) =
      ∏ j : Fin N,
        Real.exp (-(lam *
          (annulusContribution rIn rOut target (sample j) : ℝ))) := by
  have hsum :
      -(lam * (sampleTotalContribution rIn rOut target sample : ℝ)) =
        ∑ j : Fin N,
          -(lam * (annulusContribution rIn rOut target (sample j) : ℝ)) := by
    simp [sampleTotalContribution, Finset.mul_sum]
  calc
    Real.exp (-(lam * (sampleTotalContribution rIn rOut target sample : ℝ)))
        = Real.exp
          (∑ j : Fin N,
            -(lam * (annulusContribution rIn rOut target (sample j) : ℝ))) := by
          rw [hsum]
    _ = ∏ j : Fin N,
        Real.exp (-(lam *
          (annulusContribution rIn rOut target (sample j) : ℝ))) := by
          simpa using
            (Real.exp_sum Finset.univ
              (fun j : Fin N =>
                -(lam * (annulusContribution rIn rOut target (sample j) : ℝ))))
end PebblingLean.Hypercube
