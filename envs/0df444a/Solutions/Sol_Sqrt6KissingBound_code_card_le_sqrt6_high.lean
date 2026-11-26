-- Prove2me | solution 1 for Sqrt6KissingBound.code_card_le_sqrt6_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:30:38.054818+00:00
-- url     : https://prove2.me/submissions/b55e7511-20a0-4f7a-a42c-199d123fe1b4

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_BiconeBounds
import Theorems.Thm_Sqrt6KissingBound_bicone_packing_inequality
import Theorems.Thm_Sqrt6KissingBound_dimension_mul_two_pow_le_sqrt6_pow
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_antitone_from_six
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_pos
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution {k : ℕ} (hk : 4 ≤ k)
    (X : Finset (EuclideanSpace ℝ (Fin (k + 2))))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ (k + 2) := by
  let D : ℝ := (k + 2) * 2 ^ (k + 1)
  let V : ℝ := unitBallVolumeReal (k + 1)
  have hpack := bicone_packing_inequality k X hunit hsep
  change (X.card : ℝ) * ((1 / D) * V) ≤ unitBallVolumeReal (k + 2) at hpack
  have hvol : unitBallVolumeReal (k + 2) ≤ V := by
    simpa only [V, show (k + 2) - 1 = k + 1 by omega]
      using unitBallVolumeReal_antitone_from_six (k + 2) (by omega)
  have hVpos : 0 < V := by simpa only [V] using unitBallVolumeReal_pos k
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hcardD : (X.card : ℝ) ≤ D := by
    have hsmall : ((X.card : ℝ) / D) * V ≤ 1 * V := by
      calc
        ((X.card : ℝ) / D) * V = (X.card : ℝ) * ((1 / D) * V) := by ring
        _ ≤ unitBallVolumeReal (k + 2) := hpack
        _ ≤ 1 * V := by simpa using hvol
    have hratio := (mul_le_mul_iff_of_pos_right hVpos).mp hsmall
    exact (div_le_one hDpos).mp hratio
  have hnum := dimension_mul_two_pow_le_sqrt6_pow (k + 2) (by omega)
  apply hcardD.trans
  simpa only [D, show (k + 2) - 1 = k + 1 by omega, Nat.cast_add, Nat.cast_ofNat] using hnum
end Sqrt6KissingBound
