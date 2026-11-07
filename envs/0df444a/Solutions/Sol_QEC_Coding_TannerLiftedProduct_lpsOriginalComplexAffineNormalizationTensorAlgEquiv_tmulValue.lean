-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexAffineNormalizationTensorAlgEquiv_tmulValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:36:15.188645+00:00
-- url     : https://prove2.me/submissions/977dc66b-c6cc-4728-9799-a59b34d5588b

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

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary040
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary041
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary042
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary043
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
local notation "BP" => ℂ ⊗[ℚ] Polynomial ℚ
local notation "TB" => ℂ ⊗[ℚ] FQ
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary044
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary045
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary046
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary047
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary048
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary049
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary050
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary051
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary052
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary053
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (c : ℂ) (x : integralClosure (Polynomial ℚ) FQ) :
    (lpsOriginalComplexAffineNormalizationTensorAlgEquiv N hN (c ⊗ₜ[ℚ] x)).val =
      algebraMap ℂ FC c * lpsOriginalGeneratedQToComplex N hN x.val :=
  lpsOriginalComplexAffineNormalizationTensorEquiv_tmulValue N hN c x
end QEC.Coding.TannerLiftedProduct
