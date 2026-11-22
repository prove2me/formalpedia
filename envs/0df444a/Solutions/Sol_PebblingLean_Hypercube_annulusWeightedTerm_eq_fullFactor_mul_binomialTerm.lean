-- Prove2me | solution 1 for PebblingLean.Hypercube.annulusWeightedTerm_eq_fullFactor_mul_binomialTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:03:59.048801+00:00
-- url     : https://prove2.me/submissions/97629187-8c2f-43f2-ad92-c48167de1914

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
theorem _root_.solution
    {n rOut i : ℕ} (hin : i ≤ n) (hr : i ≤ rOut) :
    (2 ^ (rOut - i) : ℝ) / (2 ^ n : ℝ) =
      (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
        ((((1 : ℝ) / 3) ^ i) * (((2 : ℝ) / 3) ^ (n - i))) := by
  have hpow_r : (2 : ℝ) ^ rOut = (2 : ℝ) ^ (rOut - i) * (2 : ℝ) ^ i := by
    rw [← pow_add]
    simp_all
  have hpow_n : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - i) * (2 : ℝ) ^ i := by
    rw [← pow_add]
    simp_all
  have hpow3_n : (3 : ℝ) ^ n = (3 : ℝ) ^ (n - i) * (3 : ℝ) ^ i := by
    rw [← pow_add]
    simp_all
  have hfour_n :
      (4 : ℝ) ^ n = (2 : ℝ) ^ (i * 2) * (2 : ℝ) ^ ((n - i) * 2) := by
    calc
      (4 : ℝ) ^ n = ((2 : ℝ) ^ 2) ^ n := by norm_num
      _ = (2 : ℝ) ^ (2 * n) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (i * 2 + (n - i) * 2) := by
            congr
            omega
      _ = (2 : ℝ) ^ (i * 2) * (2 : ℝ) ^ ((n - i) * 2) := by rw [pow_add]
  simp only [div_pow]
  field_simp [pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0),
    pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0)]
  rw [hpow_r, hpow_n, hpow3_n]
  rw [hfour_n]
  ring
end PebblingLean.Hypercube
