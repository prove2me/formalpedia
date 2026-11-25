-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_capSet_68dd2d8398ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:48.136164+00:00
-- url     : https://prove2.me/submissions/33ced44d-453a-45dd-8c3a-f9d5111f9af6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawFirstCoord
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_annulus_c7db0dfdc2da
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_continuous_sqNorm_309bdd8d6577
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_piFinSuccAbove_zero_apply_389038ca931c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_nonneg_b8444e370306
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_succ_4c218d8f435d


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
open MeasureTheory ProbabilityTheory Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereLawFirstCoord
open SphereMean
namespace GroundTheory.Heights₂.Heights.SphereLawFirstCoord
theorem _root_.solution {m : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    volume {v : Fin (m + 1) → ℂ | c * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} =
      (∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y / (1 - c))) * NNReal.pi := by
  have h1c : 0 < 1 - c := by linarith
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℂ) 0
  set A : Set (ℂ × (Fin m → ℂ)) :=
    {p | c * (‖p.1‖ ^ 2 + sqNorm p.2) ≤ ‖p.1‖ ^ 2 ∧ ‖p.1‖ ^ 2 + sqNorm p.2 < 1} with hA_def
  have hA : MeasurableSet A := by
    have h1 : Continuous fun p : ℂ × (Fin m → ℂ) ↦ ‖p.1‖ ^ 2 + sqNorm p.2 :=
      ((continuous_norm.comp continuous_fst).pow 2).add ((continuous_sqNorm m).comp continuous_snd)
    exact (measurableSet_le (continuous_const.mul h1).measurable
      ((continuous_norm.comp continuous_fst).pow 2).measurable).inter
      (measurableSet_lt h1.measurable measurable_const)
  have hpre : {v : Fin (m + 1) → ℂ | c * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} =
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℂ) 0 ⁻¹' A := by
    ext v
    simp only [mem_ofPred_eq, mem_preimage, piFinSuccAbove_zero_apply, hA_def, sqNorm_succ]
  rw [hpre, he.measure_preimage hA.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_apply_symm hA, ← lintegral_mul_const' _ _ ENNReal.coe_ne_top]
  congr 1
  funext y
  have hfib : (fun x : ℂ ↦ (x, y)) ⁻¹' A =
      {w : ℂ | c * sqNorm y / (1 - c) ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 < 1 - sqNorm y} := by
    ext w
    simp only [mem_preimage, hA_def, mem_ofPred_eq, div_le_iff₀ h1c]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
  rw [hfib, volume_annulus (div_nonneg (mul_nonneg hc0 (sqNorm_nonneg y)) h1c.le)]
  congr 2
  field_simp
  ring
end GroundTheory.Heights₂.Heights.SphereLawFirstCoord
