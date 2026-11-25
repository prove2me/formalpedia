-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.HE.levi_logNormSq_zero_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:33:58.444461+00:00
-- url     : https://prove2.me/submissions/b7c6e723-8785-40fb-89d8-03af93e589d9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.HE
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Filter Complex
open scoped ContDiff ComplexConjugate Matrix
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE
theorem _root_.solution (g : V n → ℂ) (v0 : V n) (hg : ContDiffAt ℂ 2 g v0)
    (hne : g v0 ≠ 0) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((Real.log (Complex.normSq (g y)) : ℝ) : ℂ)) v0 ξ = 0 := by
  have hev1 : ∀ᶠ y in 𝓝 v0, ContDiffAt ℂ 2 g y := hg.eventually (by norm_num)
  have hev2 : ∀ᶠ y in 𝓝 v0, g y ≠ 0 := hg.continuousAt.eventually_ne hne
  have hwdb : ∀ k, wdb n k (fun y => ((Real.log (Complex.normSq (g y)) : ℝ) : ℂ)) =ᶠ[𝓝 v0]
      fun y => starRingEnd ℂ (fderiv ℂ g y (bas n k) / g y) := by
    intro k
    filter_upwards [hev1, hev2] with y hy1 hy2
    have hdg : HasFDerivAt g ((fderiv ℂ g y).restrictScalars ℝ) y :=
      ((hy1.differentiableAt (by norm_num)).hasFDerivAt).restrictScalars ℝ
    have hre : HasFDerivAt (fun w => (g w).re)
        (Complex.reCLM.comp ((fderiv ℂ g y).restrictScalars ℝ)) y :=
      Complex.reCLM.hasFDerivAt.comp y hdg
    have him : HasFDerivAt (fun w => (g w).im)
        (Complex.imCLM.comp ((fderiv ℂ g y).restrictScalars ℝ)) y :=
      Complex.imCLM.hasFDerivAt.comp y hdg
    have hN := (hre.mul hre).add (him.mul him)
    have hpos : 0 < (g y).re * (g y).re + (g y).im * (g y).im := by
      rw [← Complex.normSq_apply]
      exact Complex.normSq_pos.mpr hy2
    have hh := (Complex.ofRealCLM.hasFDerivAt.comp y (hN.log hpos.ne')).congr_of_eventuallyEq
      (f₁ := fun w => ((Real.log (Complex.normSq (g w)) : ℝ) : ℂ))
      (Filter.Eventually.of_forall fun w => by simp [Complex.normSq_apply])
    simp only [wdb]
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_restrictScalars',
      Complex.reCLM_apply, Complex.imCLM_apply, Complex.ofRealCLM_apply, smul_eq_mul, map_smul]
    have hz0 : (g y).re * (g y).re + (g y).im * (g y).im ≠ 0 := hpos.ne'
    apply Complex.ext <;>
      simp [Complex.div_re, Complex.div_im, Complex.normSq_apply] <;>
      field_simp <;>
      ring
  have hgd : DifferentiableAt ℂ g v0 := hg.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℂ (fderiv ℂ g) v0 :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hwd : ∀ j k, wd n j (wdb n k (fun y => ((Real.log (Complex.normSq (g y)) : ℝ) : ℂ))) v0 = 0 := by
    intro j k
    have hφ : DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n k) / g y) v0 := by
      have hm := (hD.clm_apply (differentiableAt_const (bas n k))).mul (hgd.inv hne)
      simp only [div_eq_mul_inv]
      exact hm
    have hc : HasFDerivAt (fun y => starRingEnd ℂ (fderiv ℂ g y (bas n k) / g y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
          ((fderiv ℂ (fun y => fderiv ℂ g y (bas n k) / g y) v0).restrictScalars ℝ)) v0 :=
      (Complex.conjCLE.hasFDerivAt.comp v0 (hφ.hasFDerivAt.restrictScalars ℝ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun w => by simp)
    simp only [wd]
    rw [(hwdb k).fderiv_eq, hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      map_smul, smul_eq_mul, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
      Complex.conj_I]
    simp [← mul_assoc, Complex.I_mul_I]
  unfold leviV
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  rw [hwd j k]
  ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
