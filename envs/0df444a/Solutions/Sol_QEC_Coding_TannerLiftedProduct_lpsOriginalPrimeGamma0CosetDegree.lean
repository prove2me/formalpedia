-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGamma0CosetDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:42:29.225717+00:00
-- url     : https://prove2.me/submissions/85f5dcb9-9f3c-4be8-b0fd-92f17e0caeb9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0OneTop
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersection_index
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)=p+1 := by
  have hone : (CongruenceSubgroup.Gamma0 1 : Subgroup (GL (Fin 2) ℝ))=𝒮ℒ := by
    change (CongruenceSubgroup.Gamma0 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)=_
    rw [lpsOriginalGamma0OneTop,MonoidHom.range_eq_map]
  change (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)).relIndex 𝒮ℒ=p+1
  rw [←hone]
  change ((CongruenceSubgroup.Gamma0 p).map (Matrix.SpecialLinearGroup.mapGL ℝ)).relIndex
    ((CongruenceSubgroup.Gamma0 1).map (Matrix.SpecialLinearGroup.mapGL ℝ))=p+1
  rw [Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective]
  simpa only [Subgroup.relIndex, one_mul] using lpsHeckeIntersection_index 1 p (Nat.coprime_one_right p)
end QEC.Coding.TannerLiftedProduct
