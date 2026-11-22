-- Prove2me | solution 1 for PebblingLean.Hypercube.annulusMean_eq_fullWeightedMean_mul_binomialWindowProbThird
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:05:12.76211+00:00
-- url     : https://prove2.me/submissions/88aac283-845a-4d93-8e82-0c1868a5b045

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_annulusMean_eq_real_sum
public import Theorems.Thm_PebblingLean_Hypercube_annulusWeightedTerm_eq_fullFactor_mul_binomialTerm
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
    (n rIn rOut : ℕ) :
    (annulusMean n rIn rOut : ℝ) =
      (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
        binomialWindowProbThird n rIn rOut := by
  classical
  rw [annulusMean_eq_real_sum]
  unfold binomialWindowProbThird
  calc
    (∑ i ∈ Finset.range (n + 1),
        ((Nat.choose n i *
          if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)) /
        (2 ^ n : ℝ)
        = ∑ i ∈ Finset.range (n + 1),
            ((Nat.choose n i *
              if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ) /
              (2 ^ n : ℝ) := by
              rw [Finset.sum_div]
    _ = ∑ i ∈ Finset.range (n + 1),
          (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
            (if rIn ≤ i ∧ i ≤ rOut then
              (Nat.choose n i : ℝ) * (((1 : ℝ) / 3) ^ i) *
                (((2 : ℝ) / 3) ^ (n - i))
            else
              0) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          by_cases hbounds : rIn ≤ i ∧ i ≤ rOut
          · have hterm :=
              annulusWeightedTerm_eq_fullFactor_mul_binomialTerm
                (n := n) (rOut := rOut) (i := i) hin hbounds.2
            calc
              ((Nat.choose n i *
                if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ) /
                  (2 ^ n : ℝ)
                  = (Nat.choose n i : ℝ) *
                      ((2 ^ (rOut - i) : ℝ) / (2 ^ n : ℝ)) := by
                    simp [hbounds]
                    ring
              _ = (Nat.choose n i : ℝ) *
                    ((2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
                      ((((1 : ℝ) / 3) ^ i) * (((2 : ℝ) / 3) ^ (n - i)))) := by
                    rw [hterm]
              _ = (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
                    ((Nat.choose n i : ℝ) * (((1 : ℝ) / 3) ^ i) *
                      (((2 : ℝ) / 3) ^ (n - i))) := by ring
              _ = (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
                    (if rIn ≤ i ∧ i ≤ rOut then
                      (Nat.choose n i : ℝ) * (((1 : ℝ) / 3) ^ i) *
                        (((2 : ℝ) / 3) ^ (n - i))
                    else
                      0) := by simp [hbounds]
          · simp [hbounds]
    _ = (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
          ∑ i ∈ Finset.range (n + 1),
            (if rIn ≤ i ∧ i ≤ rOut then
              (Nat.choose n i : ℝ) * (((1 : ℝ) / 3) ^ i) *
                (((2 : ℝ) / 3) ^ (n - i))
            else
              0) := by
          rw [← Finset.mul_sum]
end PebblingLean.Hypercube
