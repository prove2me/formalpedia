-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_lintegral_scale_ed656ae4f52c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:16:23.043782+00:00
-- url     : https://prove2.me/submissions/9b908444-e978-4809-9125-b2299ea57cdc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawFirstCoord
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_finrank_fun_complex_2b35f647dbc5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_measurable_sqNorm_950a20036208
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_smul_0f1c388bb826


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
theorem _root_.solution {m : ℕ} {c : ℝ} (hc1 : c < 1) :
    ∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y / (1 - c)) =
      ENNReal.ofReal ((1 - c) ^ m) * ∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y) := by
  have h1c : 0 < 1 - c := by linarith
  have hr0 : √(1 - c) ≠ 0 := (Real.sqrt_pos.2 h1c).ne'
  set f : (Fin m → ℂ) → ENNReal := fun y ↦ ENNReal.ofReal (1 - sqNorm y / (1 - c)) with hf
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub ((measurable_sqNorm m).div_const _))
  have hfr : ∀ y, f (√(1 - c) • y) = ENNReal.ofReal (1 - sqNorm y) := by
    intro y
    simp only [hf, sqNorm_smul, Real.sq_sqrt h1c.le]
    congr 2
    field_simp
  have key : ∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y) =
      ENNReal.ofReal (((1 - c) ^ m)⁻¹) * ∫⁻ y, f y := by
    simp_rw [← hfr]
    have hmap' : ∫⁻ y, f (√(1 - c) • y) =
        ∫⁻ y, f y ∂(Measure.map (fun y : Fin m → ℂ ↦ √(1 - c) • y) volume) :=
      (lintegral_map hfm (by fun_prop)).symm
    rw [hmap', Measure.map_addHaar_smul (volume : Measure (Fin m → ℂ)) hr0, lintegral_smul_measure,
      finrank_fun_complex, pow_mul, Real.sq_sqrt h1c.le, abs_of_pos (inv_pos.2 (pow_pos h1c m))]
    rfl
  rw [key, ← mul_assoc, ← ENNReal.ofReal_mul (pow_pos h1c m).le,
    mul_inv_cancel₀ (pow_pos h1c m).ne', ENNReal.ofReal_one, one_mul]
end GroundTheory.Heights₂.Heights.SphereLawFirstCoord
