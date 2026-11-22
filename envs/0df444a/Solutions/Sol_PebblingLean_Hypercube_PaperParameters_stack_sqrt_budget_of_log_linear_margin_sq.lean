-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.stack_sqrt_budget_of_log_linear_margin_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:10:56.911826+00:00
-- url     : https://prove2.me/submissions/cdbaecce-4efb-429b-87fb-eb899c590c4a

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_linear_margin_nonneg
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
    (hlog :
      16 * Real.log (n : ℝ) ≤
        (n : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) ^ 2) :
    4 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
      (n : ℝ) *
        (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by
  let c : ℝ := Real.log ((4 : ℝ) / 3) - Real.log 2 / 3
  have hc : 0 ≤ c := by
    simpa [c] using stack_linear_margin_nonneg
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hy_nonneg : 0 ≤ (n : ℝ) * c / 4 := by positivity
  have hscaled :
      (n : ℝ) * Real.log (n : ℝ) ≤ ((n : ℝ) * c / 4) ^ 2 := by
    have hbase :
        16 * Real.log (n : ℝ) ≤ (n : ℝ) * c ^ 2 := by
      simpa [c] using hlog
    have hmul :=
      mul_le_mul_of_nonneg_left
        hbase
        (by positivity : 0 ≤ (n : ℝ) / 16)
    have hscaled' :
        (n : ℝ) * Real.log (n : ℝ) ≤
          (n : ℝ) ^ 2 * c ^ 2 * (1 / 16) := by
      ring_nf at hmul ⊢
      exact hmul
    convert hscaled' using 1
    ring
  have hsqrt :
      Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        (n : ℝ) * c / 4 := by
    rw [Real.sqrt_le_iff]
    exact ⟨hy_nonneg, hscaled⟩
  calc
    4 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
        ≤ 4 * ((n : ℝ) * c / 4) :=
          mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 4)
    _ = (n : ℝ) * c := by ring
end PebblingLean.Hypercube.PaperParameters
