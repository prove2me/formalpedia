-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchHolomorphic_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:02:00.950989+00:00
-- url     : https://prove2.me/submissions/46b518eb-6dc3-46e6-bb8f-3e990aca7675

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchSL_function
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchHolomorphic_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchSL_mem_iff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilatedExactStabilizer
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
    Function.Injective (lpsOriginalPrimeBranchHolomorphic p) := by
  intro i j h
  have he (τ : ℍ) :
      lpsOriginalJDilated p (Fact.out : p.Prime).pos
        (lpsOriginalPrimeBranchSL p i • τ)=
      lpsOriginalJDilated p (Fact.out : p.Prime).pos
        (lpsOriginalPrimeBranchSL p j • τ) := by
    simpa only [lpsOriginalPrimeBranchSL_function,lpsOriginalPrimeBranchHolomorphic_apply]
      using congrArg (fun f : LPSOriginalHolomorphicRing => f.val τ) h
  apply (lpsOriginalPrimeBranchSL_mem_iff p i j).mp
  apply (lpsOriginalJDilatedExactStabilizer p (Fact.out : p.Prime).pos _).mp
  intro τ
  simpa only [mul_smul,smul_inv_smul] using
    he ((lpsOriginalPrimeBranchSL p j)⁻¹ • τ)
end QEC.Coding.TannerLiftedProduct
