-- Prove2me | solution 1 for Sqrt6KissingBound.bicone_packing_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:29:13.749385+00:00
-- url     : https://prove2.me/submissions/9777d373-a665-4ca1-8ccb-69df5198a83e

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_BiconeBounds
import Theorems.Thm_Sqrt6KissingBound_card_mul_volumeReal_le_unitBall
import Theorems.Thm_Sqrt6KissingBound_centeredBicone_disjoint
import Theorems.Thm_Sqrt6KissingBound_centeredBicone_subset_unitBall
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_measurableSet_centeredBicone
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
import Theorems.Thm_Sqrt6KissingBound_volumeReal_centeredBicone
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution (k : ℕ)
    (X : Finset (EuclideanSpace ℝ (Fin (k + 2))))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (X.card : ℝ) * ((1 / ((k + 2) * 2 ^ (k + 1))) * unitBallVolumeReal (k + 1)) ≤
      unitBallVolumeReal (k + 2) := by
  have h := card_mul_volumeReal_le_unitBall X (centeredBicone k)
    (fun x hx => measurableSet_centeredBicone k x)
    (fun x hx => centeredBicone_subset_unitBall (hunit x hx))
    (fun x hx z hz hne => centeredBicone_disjoint
      (hunit x hx) (hunit z hz) (hsep x hx z hz hne))
    (q := (1 / ((k + 2) * 2 ^ (k + 1))) * unitBallVolumeReal (k + 1))
    (fun x hx => volumeReal_centeredBicone k x)
  simpa [unitBallVolumeReal] using h
end Sqrt6KissingBound
