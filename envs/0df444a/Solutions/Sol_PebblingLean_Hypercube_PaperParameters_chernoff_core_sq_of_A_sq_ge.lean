-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.chernoff_core_sq_of_A_sq_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:11:53.569944+00:00
-- url     : https://prove2.me/submissions/78723549-bbd2-42ee-b3fe-3bdce72af719

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_sq_ge_splitA_log
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
    {A K : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (ha_three : 3 ≤ (splitA K n : ℝ))
    (hA_sq : 16 ≤ A ^ 2) :
    12 * ((splitA K n : ℝ) + 1) * Real.log (n : ℝ) ≤
      (annulusWidthCore A K n) ^ 2 := by
  let a : ℝ := (splitA K n : ℝ)
  let L : ℝ := Real.log (n : ℝ)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.log_natCast_nonneg n
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have ha_three' : 3 ≤ a := by
    simpa [a] using ha_three
  have hcoeff : 12 * (a + 1) ≤ 16 * a := by
    nlinarith
  have hleft :
      12 * (a + 1) * L ≤ 16 * a * L := by
    exact mul_le_mul_of_nonneg_right hcoeff hL_nonneg
  have hmid :
      16 * a * L ≤ A ^ 2 * (a * L) := by
    have haL_nonneg : 0 ≤ a * L := mul_nonneg ha_nonneg hL_nonneg
    have hmul := mul_le_mul_of_nonneg_right hA_sq haL_nonneg
    nlinarith
  have hcore :=
    annulusWidthCore_sq_ge_splitA_log
      (A := A) (K := K) (n := n) hn
  calc
    12 * ((splitA K n : ℝ) + 1) * Real.log (n : ℝ)
        = 12 * (a + 1) * L := by rfl
    _ ≤ 16 * a * L := hleft
    _ ≤ A ^ 2 * (a * L) := hmid
    _ = A ^ 2 * ((splitA K n : ℝ) * Real.log (n : ℝ)) := by rfl
    _ ≤ (annulusWidthCore A K n) ^ 2 := hcore
end PebblingLean.Hypercube.PaperParameters
