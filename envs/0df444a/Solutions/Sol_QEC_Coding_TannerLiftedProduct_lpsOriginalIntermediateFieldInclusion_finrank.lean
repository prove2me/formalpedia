-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntermediateFieldInclusion_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:12:44.660474+00:00
-- url     : https://prove2.me/submissions/929fea8f-bfee-461b-a703-3cb0b04f01e8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A B : IntermediateField K L) (h : A ≤ B) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    Module.finrank A B = A.relfinrank B := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  change Module.finrank A (IntermediateField.extendScalars h) = A.relfinrank B
  exact (IntermediateField.relfinrank_eq_finrank_of_le h).symm
end QEC.Coding.TannerLiftedProduct
