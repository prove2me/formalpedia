-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGenericMeromorphicDifferentialTensorEquiv_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:45:14.755974+00:00
-- url     : https://prove2.me/submissions/b4126272-09cf-4c19-88a8-481f9ecf8855

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericMeromorphicDifferentialMap_expand
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
open scoped UpperHalfPlane TensorProduct
noncomputable section
variable (N : ℕ) (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_135
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_141
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_143
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_145
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_146
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_147
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_178
variable [NeZero N]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (r : M) (differentialForm : KaehlerDifferential ℂ K) :
    lpsOriginalGenericMeromorphicDifferentialTensorEquiv N hpos (r ⊗ₜ differentialForm) =
      r * lpsOriginalGenericMeromorphicDifferentialMap N hpos differentialForm := by
  rw [lpsOriginalGenericMeromorphicDifferentialTensorEquiv,
    LinearEquiv.trans_apply,LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul,
    lpsOriginalGenericMeromorphicDifferentialMap_expand]
  simp only [LinearEquiv.refl_apply, LinearEquiv.smulOfNeZero_apply, Algebra.smul_def]
  change lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
    (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic) *
      (lpsOriginalGenericToMeromorphicGerm N hpos
        (lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm) * r) = _
  ring
end QEC.Coding.TannerLiftedProduct
