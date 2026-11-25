-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv2_comp_real_912f4f8715ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:08.051302+00:00
-- url     : https://prove2.me/submissions/dff4f57e-434e-49c8-8695-1b968f5c5796

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PGreenMassReplaceLevi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul levi_re_analytic)
noncomputable section
variable {ι : Type} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {ψ : (ι → ℂ) → ℝ} {G G₁ : ℝ → ℝ} {g₂ : ℝ} {y : ι → ℂ}
    (hψ : ContDiffAt ℝ 2 ψ y) (hG : ∀ᶠ z in 𝓝 y, HasDerivAt G (G₁ (ψ z)) (ψ z))
    (hG₁ : HasDerivAt G₁ g₂ (ψ y)) (v w : ι → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z => G (ψ z))) y v w =
      G₁ (ψ y) * fderiv ℝ (fderiv ℝ ψ) y v w + g₂ * fderiv ℝ ψ y v * fderiv ℝ ψ y w := by
  have hev : fderiv ℝ (fun z => G (ψ z)) =ᶠ[𝓝 y] fun z => G₁ (ψ z) • fderiv ℝ ψ z := by
    filter_upwards [hG, hψ.eventually (by simp)] with z h1 h2
    exact (h1.comp_hasFDerivAt z (h2.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hD2 : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) y) y :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasFDerivAt (fun z => G₁ (ψ z)) (g₂ • fderiv ℝ ψ y) y :=
    hG₁.comp_hasFDerivAt y (hψ.differentiableAt (by norm_num)).hasFDerivAt
  have h := ((hc.smul hD2).congr_of_eventuallyEq hev).fderiv
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
end GroundTheory.Heights₂.Heights.AnalyticLimit
