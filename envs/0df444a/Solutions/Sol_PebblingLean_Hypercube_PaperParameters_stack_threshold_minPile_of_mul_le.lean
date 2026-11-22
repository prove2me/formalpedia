-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.stack_threshold_minPile_of_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:50.514151+00:00
-- url     : https://prove2.me/submissions/b4f1ede8-6622-4065-94dc-d194fa461380

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
    (hmul :
      2 * ((n : ℝ) ^ 2) * (2 ^ rOut A K n : ℝ) ≤
        (minPile (splitM K n) : ℝ) * (((4 : ℝ) / 3) ^ splitA K n)) :
    (2 ^ rOut A K n : ℝ) ≤
      (loss n / 2) * (minPile (splitM K n) : ℝ) *
        (((4 : ℝ) / 3) ^ splitA K n) := by
  let S : ℝ := (2 ^ rOut A K n : ℝ)
  let M : ℝ := (minPile (splitM K n) : ℝ) * (((4 : ℝ) / 3) ^ splitA K n)
  have hn_sq_pos : 0 < (n : ℝ) ^ 2 := by positivity
  have hden_pos : 0 < 2 * ((n : ℝ) ^ 2) := by positivity
  have hdiv : S ≤ M / (2 * ((n : ℝ) ^ 2)) := by
    rw [le_div_iff₀ hden_pos]
    simpa [S, M, mul_assoc, mul_comm, mul_left_comm] using hmul
  calc
    (2 ^ rOut A K n : ℝ) = S := rfl
    _ ≤ M / (2 * ((n : ℝ) ^ 2)) := hdiv
    _ = (loss n / 2) * (minPile (splitM K n) : ℝ) *
        (((4 : ℝ) / 3) ^ splitA K n) := by
          unfold loss
          field_simp [hn_sq_pos.ne']
          ring
end PebblingLean.Hypercube.PaperParameters
