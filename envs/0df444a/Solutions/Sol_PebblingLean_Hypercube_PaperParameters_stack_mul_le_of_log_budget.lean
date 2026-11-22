-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.stack_mul_le_of_log_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:53.543834+00:00
-- url     : https://prove2.me/submissions/855850ed-20f9-4337-842b-f7e11310ba15

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
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hlog :
      Real.log 2 + 2 * Real.log (n : ℝ) +
          (rOut A K n : ℝ) * Real.log 2 ≤
        ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 +
          (splitA K n : ℝ) * Real.log ((4 : ℝ) / 3)) :
    2 * ((n : ℝ) ^ 2) * (2 ^ rOut A K n : ℝ) ≤
      (minPile (splitM K n) : ℝ) *
        (((4 : ℝ) / 3) ^ splitA K n) := by
  let L : ℝ := 2 * ((n : ℝ) ^ 2) * (2 ^ rOut A K n : ℝ)
  let R : ℝ :=
    (minPile (splitM K n) : ℝ) * (((4 : ℝ) / 3) ^ splitA K n)
  have hL_pos : 0 < L := by
    dsimp [L]
    positivity
  have hR_pos : 0 < R := by
    dsimp [R, minPile]
    positivity
  have hlogL :
      Real.log L =
        Real.log 2 + 2 * Real.log (n : ℝ) +
          (rOut A K n : ℝ) * Real.log 2 := by
    dsimp [L]
    rw [show 2 * (n : ℝ) ^ 2 * (2 ^ rOut A K n : ℝ) =
        2 * (((n : ℝ) ^ 2) * (2 ^ rOut A K n : ℝ)) by ring]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by positivity : ((n : ℝ) ^ 2) * (2 ^ rOut A K n : ℝ) ≠ 0)]
    rw [Real.log_mul (by positivity : ((n : ℝ) ^ 2 : ℝ) ≠ 0)
      (by positivity : (2 ^ rOut A K n : ℝ) ≠ 0)]
    rw [Real.log_pow, Real.log_pow]
    ring
  have hlogR :
      Real.log R =
        ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 +
          (splitA K n : ℝ) * Real.log ((4 : ℝ) / 3) := by
    dsimp [R, minPile]
    rw [Real.log_mul
      (by positivity : ((2 ^ (splitM K n / 5) : ℕ) : ℝ) ≠ 0)
      (by positivity : (((4 : ℝ) / 3) ^ splitA K n) ≠ 0)]
    simp_all
  have hlogLR : Real.log L ≤ Real.log R := by
    simp_all
  exact (Real.log_le_log_iff hL_pos hR_pos).mp hlogLR
end PebblingLean.Hypercube.PaperParameters
