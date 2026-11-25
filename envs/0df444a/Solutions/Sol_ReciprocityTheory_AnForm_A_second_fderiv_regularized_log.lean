-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.second_fderiv_regularized_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:45.389868+00:00
-- url     : https://prove2.me/submissions/08075b7b-ad51-4eea-a85b-985551cc11b8

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv_gReg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) (ζ a b : ℂ) :
    fderiv ℝ (fderiv ℝ (gReg ε)) ζ a b =
      (‖ζ‖ ^ 2 + ε)⁻¹ * inner ℝ a b - 2 * inner ℝ ζ a * inner ℝ ζ b / (‖ζ‖ ^ 2 + ε) ^ 2 := by
  have hs : ‖ζ‖ ^ 2 + ε ≠ 0 := by positivity
  have hq : HasFDerivAt (fun y : ℂ => ‖y‖ ^ 2 + ε) (2 • innerSL ℝ ζ) ζ :=
    (hasStrictFDerivAt_norm_sq ζ).hasFDerivAt.add_const ε
  have hc := (hasFDerivAt_inv (𝕜 := ℝ) hs).comp ζ hq
  have hL : HasFDerivAt (fun y : ℂ => innerSL ℝ y) (innerSL ℝ) ζ :=
    (innerSL ℝ).hasFDerivAt
  have h := hc.smul hL
  have h' : HasFDerivAt (fun y : ℂ => (‖y‖ ^ 2 + ε)⁻¹ • innerSL ℝ y) _ ζ := h
  rw [fderiv_gReg hε, h'.fderiv]
  have hi : ∀ x y : ℂ, (innerSL ℝ x) y = x.re * y.re + x.im * y.im := fun x y => by
    rw [innerSL_apply_apply]; simp [Complex.inner]; ring
  simp [hi]
  field_simp
  ring
end ReciprocityTheory.AnForm.A
