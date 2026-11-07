-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2Difference_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:26:06.891774+00:00
-- url     : https://prove2.me/submissions/2c55965e-3295-4feb-bd79-18cf9800a510

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
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
theorem _root_.solution (m : ℕ) (hm : 0 < m) (z : ℍ) :
    lpsE2Difference m hm ((1:ℝ) +ᵥ z)=lpsE2Difference m hm z := by
  have ht : ModularGroup.T∈CongruenceSubgroup.Gamma0 m := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T,Matrix.of_apply]
  have h := congrFun (lpsE2Difference_slash_gamma0 m hm ModularGroup.T ht) z
  rw [ModularForm.SL_slash_apply,UpperHalfPlane.modular_T_smul,ModularGroup.denom_apply] at h
  simpa [ModularGroup.T,Matrix.of_apply] using h
end QEC.Coding.TannerLiftedProduct
