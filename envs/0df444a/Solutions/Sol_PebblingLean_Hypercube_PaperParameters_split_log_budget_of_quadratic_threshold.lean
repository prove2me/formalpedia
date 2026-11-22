-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.split_log_budget_of_quadratic_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:56:45.6686+00:00
-- url     : https://prove2.me/submissions/94ada252-975d-4b24-bf1c-d5d21368063b

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
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
theorem _root_.solution {K : ℝ} {n : ℕ}
    (hthreshold : (128 * K ^ 2) ^ 2 ≤ (n : ℝ)) :
    K ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) / 64 := by
  have hK2_nonneg : 0 ≤ K ^ 2 := sq_nonneg K
  have hcoef_nonneg : 0 ≤ 128 * K ^ 2 := by positivity
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hsqrt_threshold : 128 * K ^ 2 ≤ Real.sqrt (n : ℝ) := by
    have hsqrt := Real.sqrt_le_sqrt hthreshold
    simp_all
  have hlog_half :=
    Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < 1 / 2)
  have hlog_sqrt : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_eq_rpow] at hlog_half
    calc
      Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) / (1 / 2) := hlog_half
      _ = 2 * Real.sqrt (n : ℝ) := by ring
  have hlog_mul :
      K ^ 2 * Real.log (n : ℝ) ≤
        K ^ 2 * (2 * Real.sqrt (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog_sqrt hK2_nonneg
  have hsqrt_mul :
      (128 * K ^ 2) * Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hsqrt_threshold (Real.sqrt_nonneg (n : ℝ))
    simpa [Real.mul_self_sqrt hn_nonneg, mul_assoc] using hmul
  have hmain :
      K ^ 2 * (2 * Real.sqrt (n : ℝ)) ≤ (n : ℝ) / 64 := by
    nlinarith
  exact hlog_mul.trans hmain
end PebblingLean.Hypercube.PaperParameters
