-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.stack_log_linear_budget_of_quadratic_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:10:07.757203+00:00
-- url     : https://prove2.me/submissions/e0e3e054-da78-4c5e-a146-895850143885

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stackMargin_pos
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
theorem _root_.solution {n : ℕ}
    (hthreshold : (32 / stackMargin ^ 2) ^ 2 ≤ (n : ℝ)) :
    16 * Real.log (n : ℝ) ≤
      (n : ℝ) *
        (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) ^ 2 := by
  have hc_pos : 0 < stackMargin := stackMargin_pos
  have hc_sq_pos : 0 < stackMargin ^ 2 := sq_pos_of_pos hc_pos
  have hcoef_nonneg : 0 ≤ 32 / stackMargin ^ 2 := by positivity
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hsqrt_threshold : 32 / stackMargin ^ 2 ≤ Real.sqrt (n : ℝ) := by
    have hsqrt := Real.sqrt_le_sqrt hthreshold
    simp_all
  have hlog_half :=
    Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < 1 / 2)
  have hlog_sqrt : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_eq_rpow] at hlog_half
    calc
      Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) / (1 / 2) := hlog_half
      _ = 2 * Real.sqrt (n : ℝ) := by ring
  have hlog_part :
      16 * Real.log (n : ℝ) ≤ 32 * Real.sqrt (n : ℝ) := by
    nlinarith
  have h32_le :
      32 ≤ stackMargin ^ 2 * Real.sqrt (n : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hsqrt_threshold (sq_nonneg stackMargin)
    field_simp [hc_sq_pos.ne'] at hmul
    exact hmul
  have hmain :
      32 * Real.sqrt (n : ℝ) ≤ (n : ℝ) * stackMargin ^ 2 := by
    have hmul :=
      mul_le_mul_of_nonneg_right h32_le (Real.sqrt_nonneg (n : ℝ))
    calc
      32 * Real.sqrt (n : ℝ)
          ≤ (stackMargin ^ 2 * Real.sqrt (n : ℝ)) *
              Real.sqrt (n : ℝ) := hmul
      _ = (n : ℝ) * stackMargin ^ 2 := by
            rw [mul_assoc, ← pow_two, Real.sq_sqrt hn_nonneg]
            ring
  exact hlog_part.trans (by simpa [stackMargin] using hmain)
end PebblingLean.Hypercube.PaperParameters
