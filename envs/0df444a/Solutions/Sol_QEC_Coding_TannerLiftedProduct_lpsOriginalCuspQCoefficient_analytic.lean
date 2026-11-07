-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:49:28.675193+00:00
-- url     : https://prove2.me/submissions/392bc002-d827-4654-b4cf-cc17a0bf1460

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspQCoefficient_analyticAt_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (q : ℂ) (hq : ‖q‖<1) :
    AnalyticAt ℂ (lpsOriginalCuspQCoefficient N f ρ) q := by
  by_cases hzero : q=0
  · subst q
    exact lpsOriginalCuspQCoefficient_analyticAt_zero N f ρ
  let h := (lpsOriginalCuspGroup N ρ).strictWidthInfty
  let ft := CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ ρ)
  let F := UpperHalfPlane.cuspFunction h ft
  have hh : 0<h := lpsOriginalCuspGroup_width_positive N ρ
  have hp := Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ)
  have hbounded := OnePoint.isBoundedAt_infty_iff.mp
    (ModularFormClass.bdd_at_cusps ft (Subgroup.strictWidthInfty_pos_iff.mp hh))
  have hF : AnalyticAt ℂ F q :=
    (UpperHalfPlane.differentiableOn_cuspFunction_ball hh
      (SlashInvariantFormClass.periodic_comp_ofComplex ft hp)
      (ModularFormClass.holo ft) hbounded).analyticAt
      (Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball,dist_zero_right] using hq))
  have he : dslope F 0 =ᶠ[𝓝 q] (fun z => (F z-F 0)/z) := by
    have hn : ∀ᶠ z in 𝓝 q, z≠0 := isOpen_compl_singleton.mem_nhds hzero
    filter_upwards [hn] with z hz
    simp only [dslope_of_ne _ hz,slope,vsub_eq_sub,sub_zero,smul_eq_mul,div_eq_mul_inv]
    ring
  have hd : AnalyticAt ℂ (dslope F 0) q :=
    ((hF.sub analyticAt_const).div analyticAt_id hzero).congr he.symm
  exact analyticAt_const.mul hd
end QEC.Coding.TannerLiftedProduct
