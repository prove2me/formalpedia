-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.bernstein_width_mul_le_of_log_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:02.319931+00:00
-- url     : https://prove2.me/submissions/19309bea-b8a9-499e-b51f-3ac3955e67fd

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
      Real.log 128 + ((2 * annulusWidth A K n : ℕ) : ℝ) * Real.log 2 +
          Real.log ((((splitA K n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
        -4 * Real.log (n : ℝ) +
          ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2) :
    128 * (2 ^ (2 * annulusWidth A K n) : ℝ) *
        (((splitA K n + 1 : ℕ) : ℝ) * Real.log 2) ≤
      (loss n) ^ 2 * (minPile (splitM K n) : ℝ) := by
  let C : ℝ := (((splitA K n + 1 : ℕ) : ℝ) * Real.log 2)
  let L : ℝ := 128 * (2 ^ (2 * annulusWidth A K n) : ℝ) * C
  let R : ℝ := (loss n) ^ 2 * (minPile (splitM K n) : ℝ)
  have hlog2_pos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have hL_pos : 0 < L := by
    dsimp [L, C]
    positivity
  have hR_pos : 0 < R := by
    dsimp [R, loss, minPile]
    positivity
  have hlogL :
      Real.log L =
        Real.log 128 + ((2 * annulusWidth A K n : ℕ) : ℝ) * Real.log 2 +
          Real.log C := by
    dsimp [L]
    rw [show 128 * (2 ^ (2 * annulusWidth A K n) : ℝ) * C =
        128 * ((2 ^ (2 * annulusWidth A K n) : ℝ) * C) by ring]
    rw [Real.log_mul (by norm_num : (128 : ℝ) ≠ 0)
      (by positivity : (2 ^ (2 * annulusWidth A K n) : ℝ) * C ≠ 0)]
    rw [Real.log_mul
      (by positivity : (2 ^ (2 * annulusWidth A K n) : ℝ) ≠ 0)
      (by positivity : C ≠ 0)]
    rw [Real.log_pow]
    ring_nf
  have hlogR :
      Real.log R =
        -4 * Real.log (n : ℝ) +
          ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 := by
    dsimp [R, loss, minPile]
    rw [Real.log_mul
      (by positivity : ((((n : ℝ) ^ 2)⁻¹) ^ 2) ≠ 0)
      (by positivity : ((2 ^ (splitM K n / 5) : ℕ) : ℝ) ≠ 0)]
    rw [Real.log_pow]
    rw [Real.log_inv]
    rw [Real.log_pow]
    rw [Nat.cast_pow]
    rw [Real.log_pow]
    ring_nf
  have hlogLR : Real.log L ≤ Real.log R := by
    rw [hlogL, hlogR]
    simpa [C] using hlog
  exact (Real.log_le_log_iff hL_pos hR_pos).mp hlogLR
end PebblingLean.Hypercube.PaperParameters
