-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_zero_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:49:48.07959+00:00
-- url     : https://prove2.me/submissions/0407f9b0-8b92-4871-833b-be1a9bf15e6f

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
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) : lpsOriginalCuspQCoefficient N (f+g) ρ 0=
      lpsOriginalCuspQCoefficient N f ρ 0+lpsOriginalCuspQCoefficient N g ρ 0 := by
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let h := (lpsOriginalCuspGroup N ρ).strictWidthInfty
  let ft := CuspForm.translate f r
  let gt := CuspForm.translate g r
  have hh : 0<h := lpsOriginalCuspGroup_width_positive N ρ
  have hp := Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ)
  have ha := ModularFormClass.analyticAt_cuspFunction_zero ft hh hp
  have hb := ModularFormClass.analyticAt_cuspFunction_zero gt hh hp
  have he : UpperHalfPlane.cuspFunction h (((f+g:_) : ℍ→ℂ) ∣[(2:ℤ)] r)=
      UpperHalfPlane.cuspFunction h ft + UpperHalfPlane.cuspFunction h gt := by
    rw [FunLike.coe_add,SlashAction.add_slash]
    exact ModularForm.cuspFunction_add hh hp ft gt
  simp only [lpsOriginalCuspQCoefficient,dslope_same]
  rw [he,deriv_add ha.differentiableAt hb.differentiableAt,mul_add]
  rfl
end QEC.Coding.TannerLiftedProduct
