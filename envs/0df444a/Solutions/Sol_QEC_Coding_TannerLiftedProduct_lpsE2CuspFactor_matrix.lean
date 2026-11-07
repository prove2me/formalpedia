-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2CuspFactor_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:01:20.747713+00:00
-- url     : https://prove2.me/submissions/4fcaaec5-55a7-40aa-91f9-62a0c52c05bf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (g q r A B C D : ℝ) (hg : g≠0) (hq : q≠0)
    (ha : A*g=r+1) (hc : C*g=q) (hd : A*D-B*C=1) :
    !![r+1,r/q;q,1]=!![A,B;C,D]*!![g,D*r/q-B;0,g⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply] using ha.symm
  · simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    change r/q=A*(D*r/q-B)+B*g⁻¹
    field_simp [hg,hq]
    linear_combination -r*g*hd - B*r*hc + B*q*ha
  · simpa [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply] using hc.symm
  · simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    change 1=C*(D*r/q-B)+D*g⁻¹
    field_simp [hg,hq]
    linear_combination -q*g*hd + D*q*ha - D*r*hc
end QEC.Coding.TannerLiftedProduct
