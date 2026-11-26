-- Prove2me | solution 1 for Sqrt6KissingBound.code_card_le_fourteen_dim_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:28:55.604621+00:00
-- url     : https://prove2.me/submissions/7eb322bd-b3a6-4437-86b6-53be678ca29d

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree
import Theorems.Thm_Sqrt6KissingBound_measurableSet_standardBody3
import Theorems.Thm_Sqrt6KissingBound_standardBody3_subset
import Theorems.Thm_Sqrt6KissingBound_volumeReal_standardBody3
import Theorems.Thm_Sqrt6KissingBound_card_mul_volumeReal_le_unitBall
import Theorems.Thm_Sqrt6KissingBound_centeredBody_disjoint
import Theorems.Thm_Sqrt6KissingBound_centeredBody_subset_unitBall
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_measurableSet_centeredBody
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_three
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_two
import Theorems.Thm_Sqrt6KissingBound_volumeReal_centeredBody
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis


section
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
private lemma sqrt3_lt_26_div_15 : (Real.sqrt 3 : ℝ) < 26 / 15 := by
  have hnonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  nlinarith
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution
    (X : Finset (EuclideanSpace ℝ (Fin 3)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    X.card ≤ 14 := by
  let q : ℝ := ((2 - s3_d3) / 3) * unitBallVolumeReal 2
  have hpack := card_mul_volumeReal_le_unitBall X
    (centeredBody 1 standardBody3)
    (fun x hx => measurableSet_centeredBody measurableSet_standardBody3 x)
    (fun x hx => centeredBody_subset_unitBall standardBody3_subset (hunit x hx))
    (fun x hx z hz hne => centeredBody_disjoint standardBody3_subset
      (hunit x hx) (hunit z hz) (hsep x hx z hz hne))
    (q := q)
    (fun x hx => by
      rw [volumeReal_centeredBody measurableSet_standardBody3, volumeReal_standardBody3])
  change (X.card : ℝ) * q ≤ unitBallVolumeReal 3 at hpack
  have hT : (4 : ℝ) / 45 < (2 - s3_d3) / 3 := by
    nlinarith [sqrt3_lt_26_div_15]
  have hqbig : 4 * Real.pi / 45 < q := by
    dsimp [q]
    rw [unitBallVolumeReal_two]
    have h := mul_lt_mul_of_pos_right hT Real.pi_pos
    nlinarith
  have hqpos : 0 < q := lt_trans (by positivity) hqbig
  rw [unitBallVolumeReal_three] at hpack
  have hcR : (X.card : ℝ) < 15 := by
    by_contra hnot
    have hc : (15 : ℝ) ≤ X.card := le_of_not_gt hnot
    have hlower := mul_le_mul_of_nonneg_right hc hqpos.le
    nlinarith
  have hcN : X.card < 15 := by exact_mod_cast hcR
  omega
end Sqrt6KissingBound
