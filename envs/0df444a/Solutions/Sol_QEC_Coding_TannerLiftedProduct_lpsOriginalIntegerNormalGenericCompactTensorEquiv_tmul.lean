-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGenericCompactTensorEquiv_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:19:15.380699+00:00
-- url     : https://prove2.me/submissions/6f08dccf-b2d0-4e50-a828-7de63b899865

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalCompactMeromorphicTensorEquiv_tmul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
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
open scoped TensorProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6e81b77173_97
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6e81b77173_99
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6e81b77173_101
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6e81b77173_103
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hpos
    letI := (lpsOriginalIntegerNormalGenericJFractionEmbedding N hpos).toAlgebra
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    ∀ (r : FractionRing (Polynomial ℂ))
      (x : (lpsOriginalIntegerNormalGluedScheme N hpos).functionField),
    lpsOriginalIntegerNormalGenericCompactTensorEquiv N hpos hN
      (r ⊗ₜ[FractionRing (Polynomial ℚ)] x) =
      r • lpsOriginalGeneratedCompactMeromorphicAlgEquiv N hpos hN
        (lpsOriginalGeneratedQToComplex N hpos
          (lpsOriginalIntegerNormalGenericFunctionFieldAlgEquiv N hpos x)) := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hpos
  let := (lpsOriginalIntegerNormalGenericJFractionEmbedding N hpos).toAlgebra
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  intro r x
  change lpsOriginalRationalCompactMeromorphicTensorEquiv N hpos hN
    ((Algebra.TensorProduct.congr
      (AlgEquiv.refl : FractionRing (Polynomial ℂ) ≃ₐ[FractionRing (Polynomial ℂ)]
        FractionRing (Polynomial ℂ))
      (lpsOriginalIntegerNormalGenericFunctionFieldAlgEquiv N hpos))
      (r ⊗ₜ[FractionRing (Polynomial ℚ)] x)) = _
  simp only [Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom]
  exact lpsOriginalRationalCompactMeromorphicTensorEquiv_tmul N hpos hN r _
end QEC.Coding.TannerLiftedProduct
