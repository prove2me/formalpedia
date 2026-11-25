-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_integral_cond_linearEquiv_66821f484f1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:09.857237+00:00
-- url     : https://prove2.me/submissions/37586a12-f5d9-474c-9334-64ba7aebf67c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_map_equiv_0dc281ebe645
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_smul_f954aab74cd5

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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution (E : (Fin k × Fin n → ℂ) ≃ₗ[ℝ] (Fin k × Fin n → ℂ))
    (s : Set (Fin k × Fin n → ℂ)) (G : (Fin k × Fin n → ℂ) → ℝ) (hG : Measurable G) :
    ∫ u, G (E u) ∂cond volume (E ⁻¹' s) = ∫ x, G x ∂cond volume s := by
  let F : (Fin k × Fin n → ℂ) ≃ᵐ (Fin k × Fin n → ℂ) :=
    E.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hFE : ⇑F = ⇑E.toLinearMap := by
    funext x
    rfl
  have hc := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Fin k × Fin n → ℂ))) (f := E.toLinearMap) E.isUnit_det'.ne_zero
  have hc0 : ENNReal.ofReal |(LinearMap.det E.toLinearMap)⁻¹| ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.mpr (inv_ne_zero E.isUnit_det'.ne_zero)
  show ∫ u, G (F u) ∂cond volume (F ⁻¹' s) = _
  rw [← integral_map F.measurable.aemeasurable hG.aestronglyMeasurable, cond_map_equiv, hFE, hc,
    cond_smul _ _ hc0 ENNReal.ofReal_ne_top]
end GroundTheory.Heights₂.Heights.ObjectsHeight
