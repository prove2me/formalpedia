-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedTraceBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:19:21.570129+00:00
-- url     : https://prove2.me/submissions/92acae0f-80af-44c2-9fef-82cfb8233c7c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureScalarExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_finiteDimensional


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary001
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary004
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (x : lpsOriginalGeneratedFunctionFieldQ N hN) :
    Algebra.trace (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN)
      (lpsOriginalGeneratedQToComplex N hN x) =
    lpsOriginalJBaseQToC
      (Algebra.trace (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN) x) := by
  let : FiniteDimensional (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hN
  have h := QEC.Coding.OriginalNormalizationComparison.TraceComparison.trace_tensor_equiv
    (lpsOriginalRationalComplexTensorEquiv N hN) x
  change Algebra.trace (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN)
    (lpsOriginalRationalComplexTensorMap N hN ((1 : FractionRing (Polynomial ℂ))
      ⊗ₜ[FractionRing (Polynomial ℚ)] x)) =
    lpsOriginalJBaseQToC
      (Algebra.trace (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN) x) at h
  rw [lpsOriginalRationalComplexTensorMap_tmul, one_smul] at h
  exact h
end QEC.Coding.TannerLiftedProduct
