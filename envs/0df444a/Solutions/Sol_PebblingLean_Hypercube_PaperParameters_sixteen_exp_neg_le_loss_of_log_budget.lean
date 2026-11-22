-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.sixteen_exp_neg_le_loss_of_log_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:19.490682+00:00
-- url     : https://prove2.me/submissions/ccc55d94-7ab5-4562-94dd-f3f7c6bd2741

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
theorem _root_.solution {n : ℕ} {E : ℝ}
    (hn : 0 < n)
    (hlog : Real.log 16 + 2 * Real.log (n : ℝ) ≤ E) :
    16 * Real.exp (-E) ≤ loss n := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn_sq_pos : 0 < (n : ℝ) ^ 2 := by positivity
  have hmul : 16 * ((n : ℝ) ^ 2) ≤ Real.exp E := by
    have hexp := Real.exp_le_exp.mpr hlog
    have heq :
        Real.exp (Real.log 16 + 2 * Real.log (n : ℝ)) =
          16 * ((n : ℝ) ^ 2) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
      rw [show Real.exp (2 * Real.log (n : ℝ)) = (n : ℝ) ^ 2 by
        rw [show 2 * Real.log (n : ℝ) =
            Real.log (n : ℝ) + Real.log (n : ℝ) by ring]
        simp [Real.exp_add, Real.exp_log hn_pos, sq]]
    simpa [heq] using hexp
  have hexp_pos : 0 < Real.exp E := Real.exp_pos E
  have htarget : 16 / Real.exp E ≤ 1 / ((n : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ hexp_pos hn_sq_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  unfold loss
  calc
    16 * Real.exp (-E) = 16 / Real.exp E := by
      rw [Real.exp_neg]
      ring
    _ ≤ 1 / ((n : ℝ) ^ 2) := htarget
    _ = (((n : ℝ) ^ 2)⁻¹) := by ring
end PebblingLean.Hypercube.PaperParameters
