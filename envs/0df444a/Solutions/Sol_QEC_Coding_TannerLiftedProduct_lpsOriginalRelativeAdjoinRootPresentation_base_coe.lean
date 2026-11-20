-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeAdjoinRootPresentation_base_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:21:50.381399+00:00
-- url     : https://prove2.me/submissions/8e8ad480-ca4b-4a59-ba6c-7e6cf1bd2d75

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (x : E)
    (h : K ≤ IntermediateField.adjoin F {x}) (P : Polynomial K)
    (hP : P = minpoly K x) (hx : IsIntegral K x) (c : K) :
    (((AdjoinRoot.algEquivOfEq K P _ hP).trans
      ((IntermediateField.adjoinRootEquivAdjoin K hx).trans
        (IntermediateField.equivOfEq (IntermediateField.extendScalars_adjoin h).symm))).toRingEquiv
      (algebraMap K (AdjoinRoot P) c) : E) = c := by
  change (((AdjoinRoot.algEquivOfEq K P _ hP).trans
      ((IntermediateField.adjoinRootEquivAdjoin K hx).trans
        (IntermediateField.equivOfEq (IntermediateField.extendScalars_adjoin h).symm)))
      (algebraMap K (AdjoinRoot P) c) : E) = c
  rw [AlgEquiv.commutes]
  rfl
end QEC.Coding.TannerLiftedProduct
