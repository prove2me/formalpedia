-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerZeroNormalizationRationalTensorAlgEquiv_tmulValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:35:08.731564+00:00
-- url     : https://prove2.me/submissions/4293a7c8-76bb-4507-9b01-9760be0e9fa5

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
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary054
variable (N : ℕ) (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "BP" => ℚ ⊗[ℤ] Polynomial ℤ
local notation "TB" => ℚ ⊗[ℤ] FQ
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary055
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary056
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary057
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary058
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary059
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary060
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary061
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q : ℚ) (x : integralClosure (Polynomial ℤ) FQ) :
    (lpsOriginalIntegerZeroNormalizationRationalTensorAlgEquiv N hN (q ⊗ₜ[ℤ] x)).val =
      q • x.val := lpsOriginalIntegerZeroNormalizationRationalTensorEquiv_tmulValue N hN q x
end QEC.Coding.TannerLiftedProduct
