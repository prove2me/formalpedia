-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalCompactMeromorphicTensorEquiv_jN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:18:48.905982+00:00
-- url     : https://prove2.me/submissions/dc031a0f-7530-45e5-81ea-9cafb2ee84dc

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic
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
    letI := lpsOriginalFilledTopology N
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    let αQ : lpsOriginalGeneratedFunctionFieldQ N hpos :=
      ⟨lpsOriginalJNInFractionField N hpos,
        IntermediateField.subset_adjoin (FractionRing (Polynomial ℚ))
          {lpsOriginalJNInFractionField N hpos} (Set.mem_singleton _)⟩
    (lpsOriginalRationalCompactMeromorphicTensorEquiv N hpos hN
      ((1 : FractionRing (Polynomial ℂ)) ⊗ₜ[FractionRing (Polynomial ℚ)] αQ)).val =
      (lpsOriginalFilledJDilated N hpos :
        Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) := by
  let := lpsOriginalFilledTopology N
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  dsimp only
  let αQ : lpsOriginalGeneratedFunctionFieldQ N hpos :=
    ⟨lpsOriginalJNInFractionField N hpos,
      IntermediateField.subset_adjoin (FractionRing (Polynomial ℚ))
        {lpsOriginalJNInFractionField N hpos} (Set.mem_singleton _)⟩
  let F : LPSOriginalFilledMeromorphicFunctionRing N hN :=
    ⟨lpsOriginalFilledJDilated N hpos,lpsOriginalFilledChartMeromorphic_jN N hpos hN⟩
  have he : lpsOriginalRationalCompactMeromorphicTensorEquiv N hpos hN
      ((1 : FractionRing (Polynomial ℂ)) ⊗ₜ[FractionRing (Polynomial ℚ)] αQ) =
        (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict F := by
    rw [lpsOriginalRationalCompactMeromorphicTensorEquiv_tmul,one_smul]
    apply (lpsOriginalCompactRestrictedMeromorphicEquiv N hN).injective
    change (lpsOriginalCompactRestrictedMeromorphicEquiv N hN)
      ((lpsOriginalCompactRestrictedMeromorphicEquiv N hN).symm
        (lpsOriginalGeneratedFullMeromorphicEquiv N hpos hN
          (lpsOriginalGeneratedQToComplex N hpos αQ))) =
      lpsOriginalCompactToRestrictedMeromorphic N hN
        ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict F)
    rw [RingEquiv.apply_symm_apply,lpsOriginalCompactToRestrictedMeromorphic_apply]
    apply Subtype.ext
    change lpsOriginalHolomorphicFractionToMeromorphicGerm
      (lpsOriginalJNInFractionField N hpos) =
      (lpsOriginalFilledMeromorphicRestriction N hN
        (lpsOriginalFilledJDilated N hpos)
        (lpsOriginalFilledChartMeromorphic_jN N hpos hN)).val
    rw [lpsOriginalJNInFractionField,
      lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic]
    exact (lpsOriginalFilledMeromorphicRestriction_jN N hpos hN).symm
  exact congrArg Subtype.val he
end QEC.Coding.TannerLiftedProduct
