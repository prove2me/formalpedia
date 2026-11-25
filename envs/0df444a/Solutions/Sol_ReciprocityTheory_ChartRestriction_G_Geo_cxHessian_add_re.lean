-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.cxHessian_add_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:53.137849+00:00
-- url     : https://prove2.me/submissions/44478955-7a69-48a8-8531-a3786b3cb61f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_hess_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial Filter Topology
variable {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {φ : (Fin e → ℂ) → ℝ} {G : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (C : ℝ)
    (hφ : ContDiffAt ℝ 2 φ y) (hG : AnalyticAt ℂ G y) :
    cxHessian (fun y' => φ y' + (G y').re + C) y = cxHessian φ y := by
  have hre2 : ContDiffAt ℝ 2 (fun y' => (G y').re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hG.contDiffAt.restrict_scalars ℝ)
  have hφev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ φ y' :=
    (hφ.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have hreev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ (fun y' => (G y').re) y' :=
    (hre2.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y' => φ y' + (G y').re + C) =ᶠ[𝓝 y]
      fun y' => fderiv ℝ φ y' + fderiv ℝ (fun y' => (G y').re) y' := by
    filter_upwards [hφev, hreev] with y' h1 h2
    rw [fderiv_add_const]
    exact (h1.hasFDerivAt.add h2.hasFDerivAt).fderiv
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) y :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdre : DifferentiableAt ℝ (fderiv ℝ (fun y' => (G y').re)) y :=
    (hre2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsum : fderiv ℝ (fderiv ℝ (fun y' => φ y' + (G y').re + C)) y =
      fderiv ℝ (fderiv ℝ φ) y + fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y := by
    rw [heq.fderiv_eq]
    exact (hdφ.hasFDerivAt.add hdre.hasFDerivAt).fderiv
  have hH := hess_re hG
  have k1 : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y (Complex.I • u) (Complex.I • v) =
      - fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y u v := by
    intro u v
    rw [hH, hH]
    simp [map_smul, ← mul_assoc]
  have k2 : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y u (Complex.I • v) =
      fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y (Complex.I • u) v := by
    intro u v
    rw [hH, hH]
    simp [map_smul]
  ext i j
  simp only [cxHessian, hsum, ContinuousLinearMap.add_apply, k1, k2]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.G.Geo
