-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projLine_leviForm_radial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:56.151864+00:00
-- url     : https://prove2.me/submissions/9e9eb8e9-b49a-4df0-b49b-cbd5b8087af7

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_dNormSq_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_norm_sq_eq
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_hasFDerivAt_normSq
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_continuous_normSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {F : (Fin 1 → ℂ) → ℝ} {G G' : ℝ → ℝ} {G'' : ℝ} {y : Fin 1 → ℂ}
    (hF : ∀ᶠ w in 𝓝 y, F w = G (‖w 0‖ ^ 2))
    (hG : ∀ᶠ t in 𝓝 (‖y 0‖ ^ 2), HasDerivAt G (G' t) t)
    (hG' : HasDerivAt G' G'' (‖y 0‖ ^ 2)) (v : Fin 1 → ℂ) :
    levi F y v = (G'' * ‖y 0‖ ^ 2 + G' (‖y 0‖ ^ 2)) * ‖v 0‖ ^ 2 := by
  have hqd : ∀ w : Fin 1 → ℂ, HasFDerivAt (fun w : Fin 1 → ℂ => ‖w 0‖ ^ 2) (projectiveLineNormSqDerivative w) w :=
    projLine_hasFDerivAt_normSq
  have hev : ∀ᶠ w in 𝓝 y, HasFDerivAt F (G' (‖w 0‖ ^ 2) • projectiveLineNormSqDerivative w) w := by
    have h1 : ∀ᶠ w in 𝓝 y, ∀ᶠ z in 𝓝 w, F z = G (‖z 0‖ ^ 2) := hF.eventually_nhds
    have h2 : ∀ᶠ w in 𝓝 y, HasDerivAt G (G' (‖w 0‖ ^ 2)) (‖w 0‖ ^ 2) :=
      (projLine_continuous_normSq.tendsto y).eventually hG
    filter_upwards [h1, h2] with w hw1 hw2
    exact (hw2.comp_hasFDerivAt w (hqd w)).congr_of_eventuallyEq hw1
  have hfd : fderiv ℝ F =ᶠ[𝓝 y] fun w => G' (‖w 0‖ ^ 2) • projectiveLineNormSqDerivative w :=
    hev.mono fun w hw => hw.fderiv
  have hc : HasFDerivAt (fun w : Fin 1 → ℂ => G' (‖w 0‖ ^ 2)) (G'' • projectiveLineNormSqDerivative y) y :=
    hG'.comp_hasFDerivAt y (hqd y)
  have hL : HasFDerivAt (fun w : Fin 1 → ℂ => projectiveLineNormSqDerivative w) projectiveLineNormSqDerivative y := projectiveLineNormSqDerivative.hasFDerivAt
  have h2 := (hc.smul hL).congr_of_eventuallyEq hfd
  rw [levi, h2.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, dNormSq_apply, Pi.smul_apply, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [projLine_norm_sq_eq (y 0), projLine_norm_sq_eq (v 0)]
  ring
end ReciprocityTheory.AnForm.M
