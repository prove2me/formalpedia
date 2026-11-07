-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_qParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:47:38.683523+00:00
-- url     : https://prove2.me/submissions/4efe5c89-910e-4598-ae34-6fb2306d3d4a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (τ : ℍ) :
    lpsOriginalCuspQCoefficient N f ρ
      (Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ) =
      ((lpsOriginalCuspGroup N ρ).strictWidthInfty:ℂ) *
        (((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ) /
        (((2:ℂ)*Real.pi*I)*
          Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ) := by
  have hm := lpsOriginalCuspGroup_width_positive N ρ
  let ft := CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ ρ)
  have hp := Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ)
  have hf0 := CuspFormClass.cuspFunction_apply_zero ft hm hp
  have hq := Function.Periodic.qParam_ne_zero
    (h:=(lpsOriginalCuspGroup N ρ).strictWidthInfty) (τ:ℂ)
  rw [lpsOriginalCuspQCoefficient,dslope_of_ne _ hq]
  change ((lpsOriginalCuspGroup N ρ).strictWidthInfty:ℂ)/((2:ℂ)*Real.pi*I) *
    slope (UpperHalfPlane.cuspFunction (lpsOriginalCuspGroup N ρ).strictWidthInfty ft)
      0 (Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ) = _
  rw [slope,hf0]
  simp only [vsub_eq_sub,sub_zero,smul_eq_mul]
  rw [UpperHalfPlane.eq_cuspFunction τ hm.ne'
    (SlashInvariantFormClass.periodic_comp_ofComplex ft hp)]
  have he : ft τ = ((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ := rfl
  rw [he]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring
end QEC.Coding.TannerLiftedProduct
