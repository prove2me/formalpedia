-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.sampleCountForDemand_mean_upper_of_annulusMean_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:10:58.98582+00:00
-- url     : https://prove2.me/submissions/826de1b5-4667-42f0-a55d-e5e4d2616bf3

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_nonneg
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Hypercube_annulusMean_nonneg
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
    {A K : ℝ} {n t : ℕ}
    (hloss : loss n ≤ 1)
    (hannulus_upper :
      (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ) ≤
        (2 ^ rOut A K n : ℝ) * (((3 : ℝ) / 4) ^ splitA K n))
    (hstack :
      (2 ^ rOut A K n : ℝ) ≤
        (loss n / 2) * (t : ℝ) * (((4 : ℝ) / 3) ^ splitA K n)) :
    (sampleCountForDemand A K n t : ℝ) *
      (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ) ≤
        2 * (t : ℝ) := by
  let delta : ℝ := loss n
  let pow43 : ℝ := (((4 : ℝ) / 3) ^ splitA K n)
  let pow34 : ℝ := (((3 : ℝ) / 4) ^ splitA K n)
  let S : ℝ := (2 ^ rOut A K n : ℝ)
  let mu : ℝ := (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ)
  let x : ℝ := ((1 + delta / 2) * (t : ℝ) * pow43) / S
  have hdelta_nonneg : 0 ≤ delta := by
    dsimp [delta]
    exact loss_nonneg n
  have hdelta_le : delta ≤ 1 := by
    dsimp [delta]
    exact hloss
  have hSpos : 0 < S := by
    dsimp [S]
    positivity
  have hpow_prod : pow43 * pow34 = 1 := by
    dsimp [pow43, pow34]
    rw [← mul_pow]
    norm_num
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hmu_nonneg : 0 ≤ mu := by
    dsimp [mu]
    exact annulusMean_nonneg _ _ _
  have hmu_upper : mu ≤ S * pow34 := by
    simpa [mu, S, pow34] using hannulus_upper
  have hN_le : (sampleCountForDemand A K n t : ℝ) ≤ x + 1 := by
    exact le_of_lt (by
      simpa [sampleCountForDemand, x, delta, S, pow43] using
        Nat.ceil_lt_add_one hx_nonneg)
  have hmain_le :
      (sampleCountForDemand A K n t : ℝ) * mu ≤ (x + 1) * mu :=
    mul_le_mul_of_nonneg_right hN_le hmu_nonneg
  have hxmu_le : x * mu ≤ (1 + delta / 2) * (t : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hmu_upper hx_nonneg
    calc
      x * mu ≤ x * (S * pow34) := hmul
      _ = (1 + delta / 2) * (t : ℝ) := by
        dsimp [x]
        field_simp [hSpos.ne']
        calc
          (t : ℝ) * pow43 * pow34 = (t : ℝ) * (pow43 * pow34) := by ring
          _ = (t : ℝ) * 1 := by rw [hpow_prod]
          _ = (t : ℝ) := by ring
  have hmu_slack : mu ≤ delta / 2 * (t : ℝ) := by
    have hstack' : S ≤ delta / 2 * (t : ℝ) * pow43 := by
      simpa [delta, S, pow43] using hstack
    have hpow34_nonneg : 0 ≤ pow34 := by
      dsimp [pow34]
      positivity
    have hmul := mul_le_mul_of_nonneg_right hstack' hpow34_nonneg
    calc
      mu ≤ S * pow34 := hmu_upper
      _ ≤ (delta / 2 * (t : ℝ) * pow43) * pow34 := hmul
      _ = delta / 2 * (t : ℝ) := by
        calc
          delta / 2 * (t : ℝ) * pow43 * pow34 =
              delta / 2 * (t : ℝ) * (pow43 * pow34) := by ring
          _ = delta / 2 * (t : ℝ) * 1 := by rw [hpow_prod]
          _ = delta / 2 * (t : ℝ) := by ring
  calc
    (sampleCountForDemand A K n t : ℝ) * mu ≤ (x + 1) * mu := hmain_le
    _ = x * mu + mu := by ring
    _ ≤ (1 + delta / 2) * (t : ℝ) + delta / 2 * (t : ℝ) :=
      add_le_add hxmu_le hmu_slack
    _ ≤ 2 * (t : ℝ) := by
      have ht_nonneg : 0 ≤ (t : ℝ) := by positivity
      nlinarith
end PebblingLean.Hypercube.PaperParameters
