-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.normalizedCost_recursiveCostBound_step_of_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:52.095404+00:00
-- url     : https://prove2.me/submissions/9e348e6c-8783-4960-851e-aeac9eac1b89

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_recursiveCostBound_step
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_costMultiplier_le_one_add_two_loss
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
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
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {K : ℝ} {n0 n : ℕ}
    (hn : n0 ≤ n) (hsmall : splitM K n < n)
    (hslack : 1 ≤ loss n * (((4 : ℝ) / 3) ^ splitA K n)) :
    normalizedCost (recursiveCostBound K n0) n ≤
      (1 + 2 * loss n) *
        normalizedCost (recursiveCostBound K n0) (splitM K n) := by
  unfold normalizedCost
  have hbase_pos : 0 < ((4 : ℝ) / 3) := by norm_num
  have hpow_n_pos : 0 < (((4 : ℝ) / 3) ^ n) := pow_pos hbase_pos n
  have hsplit : splitA K n + splitM K n = n := by
    unfold splitA
    exact Nat.sub_add_cancel (le_of_lt hsmall)
  have hpow_split : (((4 : ℝ) / 3) ^ n) =
      (((4 : ℝ) / 3) ^ splitA K n) *
        (((4 : ℝ) / 3) ^ splitM K n) := by
    rw [← pow_add, hsplit]
  have hmult := costMultiplier_le_one_add_two_loss (K := K) (n := n) hslack
  have hcost :
      (recursiveCostBound K n0 n : ℝ) ≤
        ((1 + 2 * loss n) * (((4 : ℝ) / 3) ^ splitA K n)) *
          (recursiveCostBound K n0 (splitM K n) : ℝ) := by
    rw [recursiveCostBound_step hn hsmall]
    have hprev_nonneg : 0 ≤ (recursiveCostBound K n0 (splitM K n) : ℝ) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hmult hprev_nonneg
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hdiv := div_le_div_of_nonneg_right hcost hpow_n_pos.le
  calc
    (recursiveCostBound K n0 n : ℝ) / (((4 : ℝ) / 3) ^ n)
        ≤ (((1 + 2 * loss n) * (((4 : ℝ) / 3) ^ splitA K n)) *
          (recursiveCostBound K n0 (splitM K n) : ℝ)) /
            (((4 : ℝ) / 3) ^ n) := hdiv
    _ = (1 + 2 * loss n) *
          ((recursiveCostBound K n0 (splitM K n) : ℝ) /
            (((4 : ℝ) / 3) ^ splitM K n)) := by
          rw [hpow_split]
          field_simp [pow_ne_zero _ hbase_pos.ne']
end PebblingLean.Hypercube.PaperParameters
