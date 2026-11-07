-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalBase_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:32:55.113124+00:00
-- url     : https://prove2.me/submissions/17872ecf-2ca5-4d9a-bd65-8ffee923ca1f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionInversion_involutive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalBaseFractionMap_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerBase_isFractionRing


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    letI := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
    IsFractionRing (Polynomial ℤ) (FractionRing (Polynomial ℚ)) := by
  let := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
  let : FaithfulSMul (Polynomial ℤ) (FractionRing (Polynomial ℚ)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      lpsOriginalIntegerReciprocalBaseFractionMap_injective
  apply IsFractionRing.of_field
  intro x
  let := lpsOriginalIntegerBaseFractionMap.toAlgebra
  let : IsFractionRing (Polynomial ℤ) (FractionRing (Polynomial ℚ)) :=
    lpsOriginalIntegerBase_isFractionRing
  obtain ⟨a,b,_,h⟩ := IsFractionRing.div_surjective (Polynomial ℤ)
    (lpsOriginalJFractionInversion x)
  change lpsOriginalIntegerBaseFractionMap a /
    lpsOriginalIntegerBaseFractionMap b=lpsOriginalJFractionInversion x at h
  refine ⟨a,b,?_⟩
  change x=lpsOriginalJFractionInversion (lpsOriginalIntegerBaseFractionMap a) /
    lpsOriginalJFractionInversion (lpsOriginalIntegerBaseFractionMap b)
  rw [←map_div₀, h,lpsOriginalJFractionInversion_involutive]
end QEC.Coding.TannerLiftedProduct
