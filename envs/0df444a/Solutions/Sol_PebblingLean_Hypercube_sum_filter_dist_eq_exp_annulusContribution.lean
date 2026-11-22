-- Prove2me | solution 1 for PebblingLean.Hypercube.sum_filter_dist_eq_exp_annulusContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:04:24.046551+00:00
-- url     : https://prove2.me/submissions/1ddabc46-8906-45f6-bf43-358a963fb2af

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_card_filter_dist_eq
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
theorem _root_.solution {n rIn rOut i : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    (∑ center ∈
        (Finset.univ.filter fun center : HypercubeVertex n => dist target center = i),
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))) =
      (Nat.choose n i : ℝ) *
        Real.exp
          (-(lam *
            ((if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ))) := by
  classical
  let sphere : Finset (HypercubeVertex n) :=
    Finset.univ.filter fun center : HypercubeVertex n => dist target center = i
  let contributionAtDistance : ℕ :=
    if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0
  have hconst :
      ∀ center ∈ sphere,
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ))) =
          Real.exp (-(lam * (contributionAtDistance : ℝ))) := by
    intro center hcenter
    have hdist_target : dist target center = i := by
      simpa [sphere] using (Finset.mem_filter.mp hcenter).2
    have hdist_center : dist center target = i := by
      simpa [dist_comm center target] using hdist_target
    by_cases hbounds : rIn ≤ i ∧ i ≤ rOut
    · simp [annulusContribution, contributionAtDistance, hdist_center, hbounds]
    · have hnot_bounds :
          ¬ (rIn ≤ dist center target ∧ dist center target ≤ rOut) := by
        simpa [hdist_center] using hbounds
      simp [annulusContribution, contributionAtDistance, hnot_bounds, hbounds]
  have hcard : sphere.card = Nat.choose n i := by
    simpa [sphere] using card_filter_dist_eq (n := n) (i := i) target
  calc
    (∑ center ∈
        (Finset.univ.filter fun center : HypercubeVertex n => dist target center = i),
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ))))
        = ∑ center ∈ sphere,
            Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ))) := by
          rfl
    _ = ∑ _center ∈ sphere,
        Real.exp (-(lam * (contributionAtDistance : ℝ))) := by
          exact Finset.sum_congr rfl hconst
    _ = (sphere.card : ℝ) *
        Real.exp (-(lam * (contributionAtDistance : ℝ))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = (Nat.choose n i : ℝ) *
        Real.exp
          (-(lam *
            ((if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ))) := by
          simp [hcard, contributionAtDistance]
end PebblingLean.Hypercube
