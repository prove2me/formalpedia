-- Prove2me | solution 1 for PI.SSE.sigmaStarEx_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:17:16.017533+00:00
-- url     : https://prove2.me/submissions/2a5327f3-f883-4633-94da-4ea14f4cb215

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatDefs
import Definitions.Def_Formalism_PeriodIntegrals_SigmaStarEx
import Definitions.Def_Formalism_PeriodIntegrals_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
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
open Complex Classical
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution (hR : ReduceBasis) (hG : GenEq) (hL : LatExt) (hA : PI.AreaLat) :
    PI.SigmaStarEx := by
  intro w₁ w₂ hw
  obtain ⟨v₁, v₂, hv₁, hlat, him, hbig⟩ := hR w₁ w₂ hw
  obtain ⟨G, hGd, hG0, hGodd, hG1, hG2⟩ := hG v₁ v₂ hv₁ him hbig
  have hApos : 0 < ((starRingEnd ℂ) v₁ * v₂).im := by
    rw [im_div_eq] at him
    exact (div_pos_iff_of_pos_right (Complex.normSq_pos.2 hv₁)).1 him
  refine ⟨G, hGd, hG0, hGodd, fun ω hω z => ?_⟩
  rw [← hlat] at hω ⊢
  have hext := hL v₁ v₂ hApos G hG1 hG2 ω hω z
  have harea := (hA v₁ v₂ hApos.ne').1
  rw [abs_of_pos hApos] at harea
  have hAc : ((((starRingEnd ℂ) v₁ * v₂).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hApos.ne'
  have key : ∀ (ψ g X Y : ℂ), X + Y = 0 → ψ * (cexp X * g) * cexp Y = ψ * g := by
    intro ψ g X Y h
    rw [show ψ * (cexp X * g) * cexp Y = ψ * g * cexp (X + Y) by rw [Complex.exp_add]; ring, h,
      Complex.exp_zero, mul_one]
  simp only [PI.U1, hext, harea, qf]
  apply key
  field_simp
  ring
end PI.SSE
