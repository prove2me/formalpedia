-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_fst_a9555f4bb05f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:57:58.426432+00:00
-- url     : https://prove2.me/submissions/6ab46016-551a-47cd-925e-90cfcb8c82b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_succ_4c218d8f435d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_piFinSuccAbove_zero_apply_389038ca931c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_continuous_sqNorm_309bdd8d6577
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_measurableSet_ballSet_d8b80531e855
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_nonneg_b8444e370306
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_af9c6325d276


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution (m : ℕ) (φ : ℂ → ENNReal) (hφ : Measurable φ) :
    ∫⁻ x in ballSet (m + 1) 1, φ (x 0) =
      (∫⁻ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal ((1 - r ^ 2) ^ m)) ‖z‖ * φ z) *
        volume (ballSet m 1) := by
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0 with he_def
  set A : Set (ℂ × (Fin m → ℂ)) := {p | ‖p.1‖ ^ 2 + sqNorm p.2 < 1} with hA_def
  have hA : MeasurableSet A :=
    measurableSet_lt ((continuous_norm.comp continuous_fst).pow 2 |>.add
      ((continuous_sqNorm m).comp continuous_snd)).measurable measurable_const
  set F : ℂ × (Fin m → ℂ) → ENNReal := A.indicator (fun p => φ p.1) with hF_def
  have hFm : Measurable F := (hφ.comp measurable_fst).indicator hA
  have hF : ∀ x, (ballSet (m + 1) 1).indicator (fun x => φ (x 0)) x = F (e x) := by
    intro x
    rw [he_def, piFinSuccAbove_zero_apply]
    simp only [hF_def, hA_def, indicator, ballSet, mem_ofPred_eq, sqNorm_succ]
  rw [← lintegral_indicator (measurableSet_ballSet _ _)]
  simp_rw [hF]
  rw [he.lintegral_comp_emb e.measurableEmbedding F, Measure.volume_eq_prod,
    lintegral_prod _ hFm.aemeasurable]
  have hm : Measurable (fun z : ℂ =>
      (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal ((1 - r ^ 2) ^ m)) ‖z‖ * φ z) :=
    (((ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun r : ℝ => (1 - r ^ 2) ^ m)).indicator
      measurableSet_Iio).comp measurable_norm).mul hφ
  rw [← lintegral_mul_const _ hm]
  · congr 1
    funext z
    have h1 : (fun w => F (z, w)) = (ballSet m (1 - ‖z‖ ^ 2)).indicator (fun _ => φ z) := by
      funext w
      simp only [hF_def, hA_def, indicator, ballSet, mem_ofPred_eq]
      congr 1
      apply propext
      constructor <;> intro h <;> linarith
    have h2 : ∫⁻ w, F (z, w) = φ z * volume (ballSet m (1 - ‖z‖ ^ 2)) := by
      rw [h1]
      exact lintegral_indicator_const (measurableSet_ballSet m _) _
    rw [h2]
    by_cases hz : ‖z‖ < 1
    · have hs : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      rw [volume_ballSet hs]
      simp only [indicator, mem_Iio, hz, ite_true]
      ring
    · have hs : ballSet m (1 - ‖z‖ ^ 2) = ∅ := by
        ext w
        simp only [ballSet, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        have := sqNorm_nonneg w
        nlinarith [norm_nonneg z]
      rw [hs]
      simp [indicator, hz]
end GroundTheory.Heights₂.Heights.SphereMean
