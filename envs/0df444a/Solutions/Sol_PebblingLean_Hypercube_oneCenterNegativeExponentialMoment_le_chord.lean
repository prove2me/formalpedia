-- Prove2me | solution 1 for PebblingLean.Hypercube.oneCenterNegativeExponentialMoment_le_chord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:05:15.40091+00:00
-- url     : https://prove2.me/submissions/ebdbd902-5f8e-4bfb-95e0-bb97294bd6e3

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_oneCenterContributionExpectationReal_eq_sum
public import Theorems.Thm_PebblingLean_FiniteProbability_exp_neg_mul_le_chord
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Hypercube_annulusContribution_le_width
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
    oneCenterNegativeExponentialMoment rIn rOut target lam ≤
      1 - (1 - Real.exp (-(lam * (2 ^ (rOut - rIn) : ℝ)))) *
        (oneCenterContributionExpectationReal rIn rOut target /
          (2 ^ (rOut - rIn) : ℝ)) := by
  classical
  let B : ℝ := (2 ^ (rOut - rIn) : ℝ)
  let q : ℝ := 1 - Real.exp (-(lam * B))
  have hBpos : 0 < B := by positivity
  have hcard_pos : 0 < (2 ^ n : ℝ) := by positivity
  have hcardF_nonneg : 0 ≤ (Fintype.card (HypercubeVertex n) : ℝ) := by positivity
  have hcard_eq : (Fintype.card (HypercubeVertex n) : ℝ) = (2 ^ n : ℝ) := by
    simp
  have hsum :
      (∑ center : HypercubeVertex n,
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))) ≤
        ∑ center : HypercubeVertex n,
          (1 - q * ((annulusContribution rIn rOut target center : ℝ) / B)) := by
    exact Finset.sum_le_sum fun center _hcenter => by
      have hz0 : 0 ≤ (annulusContribution rIn rOut target center : ℝ) := by positivity
      have hzB :
          (annulusContribution rIn rOut target center : ℝ) ≤ B := by
        simpa [B] using (by
          exact_mod_cast
            annulusContribution_le_width (rIn := rIn) (rOut := rOut) target center)
      simpa [B, q] using
        exp_neg_mul_le_chord (lam := lam) (B := B)
          (z := (annulusContribution rIn rOut target center : ℝ)) hBpos hz0 hzB
  have hsum_chord_eq :
      (∑ center : HypercubeVertex n,
          (1 - q * ((annulusContribution rIn rOut target center : ℝ) / B))) =
        (Fintype.card (HypercubeVertex n) : ℝ) -
          q * ((∑ center : HypercubeVertex n,
            (annulusContribution rIn rOut target center : ℝ)) / B) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    congr 1
    rw [Finset.sum_div]
    rw [Finset.mul_sum]
  rw [oneCenterNegativeExponentialMoment, oneCenterContributionExpectationReal_eq_sum]
  unfold uniformExpectationReal
  calc
    (∑ center : HypercubeVertex n,
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))) /
        (Fintype.card (HypercubeVertex n) : ℝ)
        ≤ (∑ center : HypercubeVertex n,
          (1 - q * ((annulusContribution rIn rOut target center : ℝ) / B))) /
          (Fintype.card (HypercubeVertex n) : ℝ) := by
          exact div_le_div_of_nonneg_right hsum hcardF_nonneg
    _ = 1 - q *
        (((∑ center : HypercubeVertex n,
          (annulusContribution rIn rOut target center : ℝ)) / (2 ^ n : ℝ)) / B) := by
          rw [hsum_chord_eq]
          rw [hcard_eq]
          field_simp [hBpos.ne', hcard_pos.ne']
end PebblingLean.Hypercube
