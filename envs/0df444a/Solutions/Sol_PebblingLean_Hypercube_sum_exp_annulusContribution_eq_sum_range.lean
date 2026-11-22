-- Prove2me | solution 1 for PebblingLean.Hypercube.sum_exp_annulusContribution_eq_sum_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:05:33.960937+00:00
-- url     : https://prove2.me/submissions/61e60a96-a2d7-4566-9938-39af55171fb3

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_sum_filter_dist_eq_exp_annulusContribution
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Hypercube_dist_le
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
theorem _root_.solution {n rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    (∑ center : HypercubeVertex n,
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))) =
      ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) *
          Real.exp
            (-(lam *
              ((if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ))) := by
  classical
  have hmaps :
      ∀ center ∈ (Finset.univ : Finset (HypercubeVertex n)),
        dist target center ∈ Finset.range (n + 1) := by
    intro center _hcenter
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (dist_le target center))
  have hfiber :=
    (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (HypercubeVertex n)))
      (t := Finset.range (n + 1))
      (g := fun center : HypercubeVertex n => dist target center)
      hmaps
      (fun center : HypercubeVertex n =>
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))))
  calc
    (∑ center : HypercubeVertex n,
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ))))
        = ∑ center ∈ (Finset.univ : Finset (HypercubeVertex n)),
            Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ))) := by
          rfl
    _ = ∑ i ∈ Finset.range (n + 1),
        ∑ center ∈ (Finset.univ : Finset (HypercubeVertex n)) with dist target center = i,
          Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ))) := by
          exact hfiber.symm
    _ = ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) *
          Real.exp
            (-(lam *
              ((if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simpa using
            sum_filter_dist_eq_exp_annulusContribution
              (n := n) (rIn := rIn) (rOut := rOut) (i := i) target lam
end PebblingLean.Hypercube
