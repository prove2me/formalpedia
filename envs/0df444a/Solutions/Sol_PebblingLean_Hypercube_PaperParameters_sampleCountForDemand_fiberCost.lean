-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.sampleCountForDemand_fiberCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:00:16.151805+00:00
-- url     : https://prove2.me/submissions/007a8534-597f-4fcd-96a3-a2816a8a37cf

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_nonneg
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
theorem _root_.solution {A K : ℝ} {n t : ℕ}
    (hstack :
      (2 ^ rOut A K n : ℝ) ≤
        (loss n / 2) * (t : ℝ) * (((4 : ℝ) / 3) ^ splitA K n)) :
    sampleCountForDemand A K n t * 2 ^ rOut A K n ≤
      t * costMultiplier K n := by
  let powTerm : ℝ := (((4 : ℝ) / 3) ^ splitA K n)
  let S : ℝ := (2 ^ rOut A K n : ℝ)
  let x : ℝ := ((1 + loss n / 2) * (t : ℝ) * powTerm) / S
  have hSpos : 0 < S := by
    dsimp [S]
    positivity
  have hpow_pos : 0 < powTerm := by
    dsimp [powTerm]
    positivity
  have hloss_nonneg : 0 ≤ loss n := loss_nonneg n
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hceil_lt : (sampleCountForDemand A K n t : ℝ) < x + 1 := by
    simpa [sampleCountForDemand, x, S, powTerm] using Nat.ceil_lt_add_one hx_nonneg
  have hleft_lt : (sampleCountForDemand A K n t : ℝ) * S < (x + 1) * S :=
    mul_lt_mul_of_pos_right hceil_lt hSpos
  have hstack' : S ≤ (loss n / 2) * (t : ℝ) * powTerm := by
    simpa [S, powTerm] using hstack
  have hmid : (x + 1) * S ≤ (1 + loss n) * (t : ℝ) * powTerm := by
    dsimp [x]
    field_simp [hSpos.ne']
    nlinarith [hstack']
  have hcost_target :
      (1 + loss n) * powTerm ≤ (costMultiplier K n : ℝ) := by
    have hle := Nat.le_ceil ((1 + loss n) * powTerm)
    simpa [costMultiplier, powTerm, mul_comm, mul_left_comm, mul_assoc] using hle
  have hright :
      (1 + loss n) * (t : ℝ) * powTerm ≤
        (t * costMultiplier K n : ℝ) := by
    have ht_nonneg : 0 ≤ (t : ℝ) := by positivity
    calc
      (1 + loss n) * (t : ℝ) * powTerm
          = (t : ℝ) * ((1 + loss n) * powTerm) := by ring
      _ ≤ (t : ℝ) * (costMultiplier K n : ℝ) :=
          mul_le_mul_of_nonneg_left hcost_target ht_nonneg
  have hreal :
      (sampleCountForDemand A K n t * 2 ^ rOut A K n : ℝ) ≤
        (t * costMultiplier K n : ℝ) := by
    have hlt :
        (sampleCountForDemand A K n t : ℝ) * S <
          (t * costMultiplier K n : ℝ) :=
      lt_of_lt_of_le hleft_lt (hmid.trans hright)
    exact le_of_lt (by simpa [S] using hlt)
  exact_mod_cast hreal
end PebblingLean.Hypercube.PaperParameters
