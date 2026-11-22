-- Prove2me | solution 1 for PebblingLean.Hypercube.Paper.CLean_eq_paper_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:13:41.0297+00:00
-- url     : https://prove2.me/submissions/28a3fa14-c590-4301-8f3e-70e34f2435b4

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Paper
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_recursiveCostBound_base
public import Theorems.Thm_PebblingLean_Hypercube_fromDiffSet_empty
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_self
public import Theorems.Thm_PebblingLean_Pebbling_size_single
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_left
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_right
public import Theorems.Thm_PebblingLean_Pebbling_weight_zero
attribute [local simp] PebblingLean.Graph.Walk.length_append
attribute [local simp] PebblingLean.Graph.Walk.length_reverse
attribute [local simp] PebblingLean.Hypercube.fromDiffSet_empty
attribute [local simp] PebblingLean.Hypercube.mem_annulus
attribute [local simp] PebblingLean.Pebbling.fibersDistribution_apply
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.single_apply_ne
attribute [local simp] PebblingLean.Pebbling.single_apply_self
attribute [local simp] PebblingLean.Pebbling.size_single
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_off
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_on
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_left
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_ne
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_right
attribute [local simp] PebblingLean.Pebbling.weight_zero



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.Paper
open Pebbling
namespace PebblingLean.Hypercube.Paper
theorem _root_.solution :
    CLean =
      Real.exp (4 / (N0 : ℝ) ^ 2) *
        ∑ j ∈ Finset.range N0,
          (2 ^ (j / 5) : ℝ) * (((3 : ℝ) / 2) ^ j) := by
  unfold CLean finiteBaseNormalizedBound normalizedCost
  have hexp :
      Real.exp (4 * PaperParameters.loss N0) =
        Real.exp (4 / (N0 : ℝ) ^ 2) := by
    simp [PaperParameters.loss, div_eq_mul_inv]
  have hsum :
      (∑ j ∈ Finset.range N0,
        (PaperParameters.recursiveCostBound (217 : ℝ) N0 j : ℝ) /
          (((4 : ℝ) / 3) ^ j)) =
        ∑ j ∈ Finset.range N0,
          (2 ^ (j / 5) : ℝ) * (((3 : ℝ) / 2) ^ j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjlt : j < N0 := Finset.mem_range.mp hj
    rw [PaperParameters.recursiveCostBound_base
      (K := (217 : ℝ)) (n0 := N0) (n := j) hjlt]
    change ((2 ^ j * 2 ^ (j / 5) : ℕ) : ℝ) /
        (((4 : ℝ) / 3) ^ j) =
      (2 ^ (j / 5) : ℝ) * (((3 : ℝ) / 2) ^ j)
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    simp only [div_pow]
    field_simp [pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0),
      pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [← pow_mul, ← pow_mul]
    rw [Nat.mul_comm]
  rw [hexp, hsum]
end PebblingLean.Hypercube.Paper
