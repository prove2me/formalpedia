-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.splitM_real_le_quarter_of_ceiling_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:55:47.234111+00:00
-- url     : https://prove2.me/submissions/9f587ade-191f-486c-b3f5-205f5408b5e9

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
    (hnonneg : 0 ≤ K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
    (hbound :
      K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1 ≤ (n : ℝ) / 4) :
    (splitM K n : ℝ) ≤ (n : ℝ) / 4 := by
  have hceil_lt :
      (splitM K n : ℝ) <
        K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1 := by
    simpa [splitM] using Nat.ceil_lt_add_one hnonneg
  exact le_trans (le_of_lt hceil_lt) hbound
end PebblingLean.Hypercube.PaperParameters
