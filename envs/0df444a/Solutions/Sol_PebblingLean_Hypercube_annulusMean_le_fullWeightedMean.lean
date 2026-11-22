-- Prove2me | solution 1 for PebblingLean.Hypercube.annulusMean_le_fullWeightedMean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:05:53.258798+00:00
-- url     : https://prove2.me/submissions/69d93887-285d-4f74-a065-47733d6bfb10

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_weightedSphereSum_half_eq
public import Theorems.Thm_PebblingLean_Hypercube_pow_two_sub_eq_mul_half_pow
public import Theorems.Thm_PebblingLean_Hypercube_annulusMean_eq_real_sum
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
theorem _root_.solution (n rIn rOut : ℕ) :
    (annulusMean n rIn rOut : ℝ) ≤
      (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) := by
  classical
  rw [annulusMean_eq_real_sum]
  have hden_pos : 0 < (2 ^ n : ℝ) := by positivity
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ((Nat.choose n i *
          if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ) ≤
        (Nat.choose n i : ℝ) * ((2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i) := by
    intro i _hi
    by_cases hbounds : rIn ≤ i ∧ i ≤ rOut
    · have hpow : (2 ^ (rOut - i) : ℝ) =
          (2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i :=
        pow_two_sub_eq_mul_half_pow hbounds.2
      simp_all
    · calc
        ((Nat.choose n i *
            if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)
            = 0 := by simp [hbounds]
        _ ≤ (Nat.choose n i : ℝ) *
              ((2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i) := by
              positivity
  have hsum :
      (∑ i ∈ Finset.range (n + 1),
        ((Nat.choose n i *
          if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)) ≤
        ∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℝ) * ((2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i) := by
    exact Finset.sum_le_sum hterm
  have hdiv := div_le_div_of_nonneg_right hsum hden_pos.le
  calc
    (∑ i ∈ Finset.range (n + 1),
        ((Nat.choose n i *
          if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)) /
        (2 ^ n : ℝ)
        ≤ (∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℝ) * ((2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i)) /
            (2 ^ n : ℝ) := hdiv
    _ = (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) := by
      have hsum_rearr :
          (∑ i ∈ Finset.range (n + 1),
              (Nat.choose n i : ℝ) * ((2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i)) =
            (2 ^ rOut : ℝ) *
              (∑ i ∈ Finset.range (n + 1),
                (Nat.choose n i : ℝ) * ((1 : ℝ) / 2) ^ i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        ring
      rw [hsum_rearr, weightedSphereSum_half_eq]
      have hratio : (((3 : ℝ) / 2) ^ n) / ((2 : ℝ) ^ n) =
          ((3 : ℝ) / 4) ^ n := by
        rw [← div_pow]
        norm_num
      calc
        ((2 ^ rOut : ℝ) * ((3 : ℝ) / 2) ^ n) / (2 ^ n : ℝ)
            = (2 ^ rOut : ℝ) * ((((3 : ℝ) / 2) ^ n) / ((2 : ℝ) ^ n)) := by
              ring
        _ = (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) := by rw [hratio]
end PebblingLean.Hypercube
