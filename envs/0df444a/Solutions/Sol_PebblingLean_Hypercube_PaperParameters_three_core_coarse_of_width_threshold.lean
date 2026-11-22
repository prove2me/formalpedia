-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.three_core_coarse_of_width_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:53.169805+00:00
-- url     : https://prove2.me/submissions/7f002580-b3ac-481d-8e3b-3314be44e7ce

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_split_core_bound_of_log_le_linear
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sqrt_three_n_log_eq
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_split_log_budget_of_quadratic_threshold
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
    {A : ℝ} {n0 n : ℕ}
    (hA : 0 ≤ A)
    (hn0_growth : 58 ≤ n0)
    (hwidthFitThreshold : (128 * (A * Real.sqrt 3) ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hn : n0 ≤ n) :
    3 * (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) ≤
      (3 : ℝ) * (n : ℝ) / 4 := by
  have hnreal : (n0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcoef_nonneg : 0 ≤ A * Real.sqrt 3 := by positivity
  have hlogLinear :
      (A * Real.sqrt 3) ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) / 64 :=
    split_log_budget_of_quadratic_threshold
      (K := A * Real.sqrt 3) (n := n)
      (hwidthFitThreshold.trans hnreal)
  have hmain' :
      (A * Real.sqrt 3) *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1 ≤
        (n : ℝ) / 4 :=
    split_core_bound_of_log_le_linear
      (K := A * Real.sqrt 3) (n := n)
      hcoef_nonneg
      (by omega : 8 ≤ n)
      hlogLinear
  have hmain :
      A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1 ≤
        (n : ℝ) / 4 := by
    rw [sqrt_three_n_log_eq n]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmain'
  nlinarith
end PebblingLean.Hypercube.PaperParameters
