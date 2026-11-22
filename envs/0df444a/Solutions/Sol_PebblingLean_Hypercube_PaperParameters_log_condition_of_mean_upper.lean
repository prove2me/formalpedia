-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.log_condition_of_mean_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:30:59.236646+00:00
-- url     : https://prove2.me/submissions/dbcb2c83-6fd8-4ac0-befa-4424fa3f4bc5

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
theorem _root_.solution {A K : ℝ} {n t : ℕ}
    (ht : 0 < t)
    (hmu_pos :
      0 < (sampleCountForDemand A K n t : ℝ) *
        (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))
    (hmu_upper :
      (sampleCountForDemand A K n t : ℝ) *
        (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ) ≤
          2 * (t : ℝ))
    (hsimple :
      ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        (loss n) ^ 2 * (t : ℝ) /
          (128 * (2 ^ (rOut A K n - rIn A K n) : ℝ))) :
    ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
      (demandGapForDemand n t) ^ 2 /
        (4 * (2 ^ (rOut A K n - rIn A K n) : ℝ) *
          ((sampleCountForDemand A K n t : ℝ) *
            (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))) := by
  let B : ℝ := (2 ^ (rOut A K n - rIn A K n) : ℝ)
  let mu : ℝ := (sampleCountForDemand A K n t : ℝ) *
    (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ)
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have ht_pos_real : 0 < (t : ℝ) := by
    exact_mod_cast ht
  have hden_pos : 0 < 4 * B * mu := by
    dsimp [mu, B]
    positivity
  have hmu_upper' : mu ≤ 2 * (t : ℝ) := by
    simpa [mu] using hmu_upper
  have hden_le : 4 * B * mu ≤ 8 * B * (t : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hmu_upper' (by positivity : 0 ≤ 4 * B)
    linarith
  have hnum_nonneg : 0 ≤ (demandGapForDemand n t) ^ 2 := sq_nonneg _
  have hfrac_mono :
      (demandGapForDemand n t) ^ 2 / (8 * B * (t : ℝ)) ≤
        (demandGapForDemand n t) ^ 2 / (4 * B * mu) :=
    div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le
  have hfrac_eq :
      (demandGapForDemand n t) ^ 2 / (8 * B * (t : ℝ)) =
        (loss n) ^ 2 * (t : ℝ) / (128 * B) := by
    dsimp [demandGapForDemand]
    field_simp [hB_pos.ne', ht_pos_real.ne']
    ring
  calc
    ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2
        ≤ (loss n) ^ 2 * (t : ℝ) / (128 * B) := by
          simpa [B] using hsimple
    _ = (demandGapForDemand n t) ^ 2 / (8 * B * (t : ℝ)) := hfrac_eq.symm
    _ ≤ (demandGapForDemand n t) ^ 2 / (4 * B * mu) := hfrac_mono
    _ = (demandGapForDemand n t) ^ 2 /
        (4 * (2 ^ (rOut A K n - rIn A K n) : ℝ) *
          ((sampleCountForDemand A K n t : ℝ) *
            (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))) := by
          rfl
end PebblingLean.Hypercube.PaperParameters
