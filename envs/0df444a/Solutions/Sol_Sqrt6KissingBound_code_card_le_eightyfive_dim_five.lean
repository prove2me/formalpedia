-- Prove2me | solution 1 for Sqrt6KissingBound.code_card_le_eightyfive_dim_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:30:37.259884+00:00
-- url     : https://prove2.me/submissions/db9ee73c-a76c-42de-99d3-34d5c2676c7c

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_BiconeBounds
import Theorems.Thm_Sqrt6KissingBound_bicone_packing_inequality
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_five
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_four


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution
    (X : Finset (EuclideanSpace ℝ (Fin 5)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    X.card ≤ 85 := by
  have hpack := bicone_packing_inequality 3 X hunit hsep
  rw [unitBallVolumeReal_four, unitBallVolumeReal_five] at hpack
  norm_num at hpack
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hcardR : (X.card : ℝ) < 86 := by
    by_contra hnot
    have hc : (86 : ℝ) ≤ X.card := le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_right hc hp.le
    nlinarith
  have hcN : X.card < 86 := by exact_mod_cast hcardR
  omega
end Sqrt6KissingBound
