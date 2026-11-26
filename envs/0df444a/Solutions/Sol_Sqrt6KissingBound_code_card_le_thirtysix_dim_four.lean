-- Prove2me | solution 1 for Sqrt6KissingBound.code_card_le_thirtysix_dim_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:28:33.506867+00:00
-- url     : https://prove2.me/submissions/60d84160-f28f-4718-811b-41fc6cf7028b

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Theorems.Thm_Sqrt6KissingBound_measurableSet_standardBody4
import Theorems.Thm_Sqrt6KissingBound_standardBody4_subset
import Theorems.Thm_Sqrt6KissingBound_volumeReal_standardBody4
import Theorems.Thm_Sqrt6KissingBound_standardBody4_profile_gt
import Theorems.Thm_Sqrt6KissingBound_card_mul_volumeReal_le_unitBall
import Theorems.Thm_Sqrt6KissingBound_centeredBody_disjoint
import Theorems.Thm_Sqrt6KissingBound_centeredBody_subset_unitBall
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_measurableSet_centeredBody
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
import Theorems.Thm_Sqrt6KissingBound_pi_lt_22_div_7
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_four
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_three
import Theorems.Thm_Sqrt6KissingBound_volumeReal_centeredBody
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
namespace Sqrt6KissingBound
theorem _root_.solution
    (X : Finset (EuclideanSpace ℝ (Fin 4)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    X.card ≤ 36 := by
  let T : ℝ := (265352 - 153195 * s3_d4) / 320
  let q : ℝ := T * unitBallVolumeReal 3
  have hpack := card_mul_volumeReal_le_unitBall X
    (centeredBody 2 standardBody4)
    (fun x hx => measurableSet_centeredBody measurableSet_standardBody4 x)
    (fun x hx => centeredBody_subset_unitBall standardBody4_subset (hunit x hx))
    (fun x hx z hz hne => centeredBody_disjoint standardBody4_subset
      (hunit x hx) (hunit z hz) (hsep x hx z hz hne))
    (q := q)
    (fun x hx => by
      rw [volumeReal_centeredBody measurableSet_standardBody4, volumeReal_standardBody4])
  change (X.card : ℝ) * q ≤ unitBallVolumeReal 4 at hpack
  rw [unitBallVolumeReal_four] at hpack
  have hT : (33 : ℝ) / 1036 < T := by simpa [T] using standardBody4_profile_gt
  have hpi : Real.pi < (22 : ℝ) / 7 := pi_lt_22_div_7
  have hTpi : 3 * Real.pi / 296 < T := by nlinarith
  have hpipos : 0 < Real.pi := Real.pi_pos
  have hqbig : Real.pi ^ 2 / 74 < q := by
    dsimp [q]
    rw [unitBallVolumeReal_three]
    have hmul := mul_lt_mul_of_pos_right hTpi (by positivity : 0 < 4 * Real.pi / 3)
    nlinarith
  have hqpos : 0 < q := lt_trans (by positivity) hqbig
  have hcardR : (X.card : ℝ) < 37 := by
    by_contra hnot
    have hc : (37 : ℝ) ≤ X.card := le_of_not_gt hnot
    have hlower : 37 * q ≤ (X.card : ℝ) * q := mul_le_mul_of_nonneg_right hc hqpos.le
    nlinarith
  have hcN : X.card < 37 := by exact_mod_cast hcardR
  omega
end Sqrt6KissingBound
