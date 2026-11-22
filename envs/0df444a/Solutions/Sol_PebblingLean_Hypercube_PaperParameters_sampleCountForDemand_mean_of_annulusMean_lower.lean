-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.sampleCountForDemand_mean_of_annulusMean_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:58:20.863088+00:00
-- url     : https://prove2.me/submissions/789302aa-8bef-4f15-ae43-9a95da30f835

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
    (hloss : loss n ≤ 2)
    (hannulus :
      (1 - loss n / 8) * (2 ^ rOut A K n : ℝ) *
          (((3 : ℝ) / 4) ^ splitA K n) ≤
        (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ)) :
    (t : ℝ) + demandGapForDemand n t ≤
      (sampleCountForDemand A K n t : ℝ) *
        (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ) := by
  let delta : ℝ := loss n
  let pow43 : ℝ := (((4 : ℝ) / 3) ^ splitA K n)
  let pow34 : ℝ := (((3 : ℝ) / 4) ^ splitA K n)
  let S : ℝ := (2 ^ rOut A K n : ℝ)
  let mu : ℝ := (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ)
  let lower : ℝ := (1 - delta / 8) * S * pow34
  let x : ℝ := ((1 + delta / 2) * (t : ℝ) * pow43) / S
  have hdelta_nonneg : 0 ≤ delta := by
    dsimp [delta]
    exact loss_nonneg n
  have hdelta_le : delta ≤ 2 := by
    dsimp [delta]
    exact hloss
  have hSpos : 0 < S := by
    dsimp [S]
    positivity
  have hpow43_pos : 0 < pow43 := by
    dsimp [pow43]
    positivity
  have hpow34_pos : 0 < pow34 := by
    dsimp [pow34]
    positivity
  have hlower_nonneg : 0 ≤ lower := by
    dsimp [lower]
    have hfactor : 0 ≤ 1 - delta / 8 := by linarith only [hdelta_le]
    positivity
  have hmu_ge : lower ≤ mu := by
    simpa [lower, mu, delta, S, pow34] using hannulus
  have hmu_nonneg : 0 ≤ mu := hlower_nonneg.trans hmu_ge
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx_le_N : x ≤ (sampleCountForDemand A K n t : ℝ) := by
    simpa [sampleCountForDemand, x, delta, S, pow43] using Nat.le_ceil x
  have htarget_lower : (t : ℝ) + demandGapForDemand n t ≤ x * lower := by
    have hpow_prod : pow43 * pow34 = 1 := by
      dsimp [pow43, pow34]
      rw [← mul_pow]
      norm_num
    have hxlower_eq :
        x * lower = (1 + delta / 2) * (1 - delta / 8) * (t : ℝ) := by
      calc
        x * lower = (((1 + delta / 2) * (t : ℝ) * pow43) / S) *
            ((1 - delta / 8) * S * pow34) := by rfl
        _ = ((1 + delta / 2) * (1 - delta / 8) * (t : ℝ)) *
            (pow43 * pow34) := by
              field_simp [hSpos.ne']
        _ = (1 + delta / 2) * (1 - delta / 8) * (t : ℝ) := by
              simp [hpow_prod]
    rw [hxlower_eq]
    change (t : ℝ) + delta * (t : ℝ) / 4 ≤
      (1 + delta / 2) * (1 - delta / 8) * (t : ℝ)
    have ht_nonneg : 0 ≤ (t : ℝ) := by positivity
    have htwo_minus : 0 ≤ 2 - delta := sub_nonneg.mpr hdelta_le
    have hprod_nonneg : 0 ≤ (t : ℝ) * delta * (2 - delta) :=
      mul_nonneg (mul_nonneg ht_nonneg hdelta_nonneg) htwo_minus
    nlinarith only [hprod_nonneg]
  calc
    (t : ℝ) + demandGapForDemand n t ≤ x * lower := htarget_lower
    _ ≤ x * mu := mul_le_mul_of_nonneg_left hmu_ge hx_nonneg
    _ ≤ (sampleCountForDemand A K n t : ℝ) * mu :=
      mul_le_mul_of_nonneg_right hx_le_N hmu_nonneg
end PebblingLean.Hypercube.PaperParameters
