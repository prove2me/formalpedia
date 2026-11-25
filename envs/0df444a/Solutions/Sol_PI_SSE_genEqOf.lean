-- Prove2me | solution 1 for PI.SSE.genEqOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:27:52.69911+00:00
-- url     : https://prove2.me/submissions/9fb7abea-1138-41e6-8c92-f123f6139eb6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_GenEqOf
import Theorems.Thm_PI_SSE_expo1
import Theorems.Thm_PI_SSE_expo2
import Theorems.Thm_PI_SSE_I_eq
import Theorems.Thm_PI_SSE_im_div_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution : GenEqOf := by
  intro hA hD v₁ v₂ hv₁ hτ h3
  have hAr : 0 < ((starRingEnd ℂ) v₁ * v₂).im := by
    have h1 := im_div_eq v₁ v₂
    have h2 : 0 < Complex.normSq v₁ := Complex.normSq_pos.mpr hv₁
    rw [h1] at hτ
    exact (div_pos_iff_of_pos_right h2).mp hτ
  have hA0 : (((starRingEnd ℂ) v₁ * v₂).im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hAr.ne'
  obtain ⟨hdiff, hodd, hone, htau, hder⟩ := hA (v₂ / v₁) hτ
  have hc : jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) ≠ 0 := hD (v₂ / v₁) hτ h3
  have h0 : th (v₂ / v₁) 0 = 0 := by
    have h := hodd 0
    rw [neg_zero] at h
    linear_combination h / 2
  refine ⟨fun z => v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) *
      (cexp (Real.pi * (starRingEnd ℂ) v₁ / (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ) * v₁) * z ^ 2) *
        th (v₂ / v₁) (z / v₁)), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((Differentiable.cexp (by fun_prop)).mul (hdiff.comp (by fun_prop))).const_mul _
  · have hf : HasDerivAt (fun z : ℂ => cexp (Real.pi * (starRingEnd ℂ) v₁ /
        (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ) * v₁) * z ^ 2)) 0 0 := by
      have h1 := ((hasDerivAt_pow 2 (0 : ℂ)).const_mul (Real.pi * (starRingEnd ℂ) v₁ /
        (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ) * v₁))).cexp
      simpa using h1
    have h1 : HasDerivAt (th (v₂ / v₁)) (jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁)) (0 / v₁) := by
      rw [zero_div, ← hder]
      exact (hdiff 0).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => z / v₁) (1 / v₁) 0 := (hasDerivAt_id (0 : ℂ)).div_const v₁
    have hh := h1.comp (0 : ℂ) h2
    have hG := (hf.mul hh).const_mul (v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁))
    refine hG.deriv.trans ?_
    simp only [Function.comp_apply, zero_div, h0, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Complex.exp_zero, one_mul]
    generalize jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) = c at *
    field_simp
  · intro z
    simp only
    rw [neg_sq, neg_div, hodd]
    ring
  · intro z
    simp only
    have e1 : (z + v₁) / v₁ = z / v₁ + 1 := by field_simp
    rw [e1, hone, expo1 v₁ ((starRingEnd ℂ) v₁) _ z hv₁ hA0, Complex.exp_add]
    unfold qf
    ring
  · intro z
    simp only
    have key := expo2 v₁ v₂ ((starRingEnd ℂ) v₁) ((starRingEnd ℂ) v₂) _ z hv₁ hA0 (I_eq v₁ v₂ hAr.ne')
    rw [add_div, htau]
    rw [show ∀ x y t : ℂ, v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) * (cexp x * -(cexp y * t)) =
        -(v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) * (cexp (x + y) * t)) from
        fun x y t => by rw [Complex.exp_add]; ring, key, Complex.exp_add]
    unfold qf
    ring
end PI.SSE
