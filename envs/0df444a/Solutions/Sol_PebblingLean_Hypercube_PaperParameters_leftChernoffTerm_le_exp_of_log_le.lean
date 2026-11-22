-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.leftChernoffTerm_le_exp_of_log_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:01:40.093908+00:00
-- url     : https://prove2.me/submissions/630a3760-53a5-4088-a0d7-ceb2f9c51a4d

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
theorem _root_.solution {A K : ℝ} {lam : ℕ → ℝ}
    {n : ℕ} {E : ℝ}
    (hlog :
      lam n * (rIn A K n : ℝ) +
          (splitA K n : ℝ) *
            Real.log (((1 : ℝ) / 3) * Real.exp (-(lam n)) +
              ((2 : ℝ) / 3)) ≤ -E) :
    leftChernoffTerm A K lam n ≤ Real.exp (-E) := by
  let b : ℝ := ((1 : ℝ) / 3) * Real.exp (-(lam n)) + ((2 : ℝ) / 3)
  have hb_pos : 0 < b := by
    dsimp [b]
    positivity
  have hpow :
      b ^ splitA K n = Real.exp ((splitA K n : ℝ) * Real.log b) := by
    calc
      b ^ splitA K n = (Real.exp (Real.log b)) ^ splitA K n := by
        rw [Real.exp_log hb_pos]
      _ = Real.exp ((splitA K n : ℝ) * Real.log b) := by
        rw [← Real.exp_nat_mul]
  calc
    leftChernoffTerm A K lam n =
        Real.exp (lam n * (rIn A K n : ℝ) +
          (splitA K n : ℝ) * Real.log b) := by
      rw [leftChernoffTerm]
      dsimp [b] at hpow ⊢
      rw [hpow, ← Real.exp_add]
    _ ≤ Real.exp (-E) := Real.exp_le_exp.mpr hlog
end PebblingLean.Hypercube.PaperParameters
