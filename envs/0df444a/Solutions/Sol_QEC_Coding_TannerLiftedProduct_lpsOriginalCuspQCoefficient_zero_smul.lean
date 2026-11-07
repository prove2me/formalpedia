-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_zero_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:50:00.60605+00:00
-- url     : https://prove2.me/submissions/6d8e8cae-7c8a-45ff-a9ad-6851c6345c67

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
    (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) : lpsOriginalCuspQCoefficient N (c • f) ρ 0=
      c*lpsOriginalCuspQCoefficient N f ρ 0 := by
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let h := (lpsOriginalCuspGroup N ρ).strictWidthInfty
  let ft := CuspForm.translate f r
  have hh : 0<h := lpsOriginalCuspGroup_width_positive N ρ
  have hp := Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ)
  have ha := ModularFormClass.analyticAt_cuspFunction_zero ft hh hp
  have hr : 0<r.val.det := by
    simp only [r,←Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.SpecialLinearGroup.det_mapGL,Units.val_one,zero_lt_one]
  have hσ : UpperHalfPlane.σ r c=c := by
    have hr' : 0<(Matrix.GeneralLinearGroup.det r : ℝ) := by
      simpa only [Matrix.GeneralLinearGroup.val_det_apply] using hr
    rw [UpperHalfPlane.σ,if_pos hr']
    rfl
  have he : UpperHalfPlane.cuspFunction h (((c • f:_) : ℍ→ℂ) ∣[(2:ℤ)] r)=
      c • UpperHalfPlane.cuspFunction h ft := by
    rw [FunLike.coe_smul,ModularForm.smul_slash]
    rw [hσ]
    exact ModularForm.cuspFunction_smul hh hp c ft
  simp only [lpsOriginalCuspQCoefficient,dslope_same]
  rw [he,deriv_const_smul c ha.differentiableAt]
  simp only [smul_eq_mul]
  change (h:ℂ)/((2:ℂ)*Real.pi*I)*(c*deriv (UpperHalfPlane.cuspFunction h ft) 0)=
    c*((h:ℂ)/((2:ℂ)*Real.pi*I)*deriv (UpperHalfPlane.cuspFunction h ft) 0)
  ring
end QEC.Coding.TannerLiftedProduct
