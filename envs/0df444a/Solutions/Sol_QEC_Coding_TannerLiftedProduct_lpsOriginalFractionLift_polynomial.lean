-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFractionLift_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:28:56.677891+00:00
-- url     : https://prove2.me/submissions/c9930aa7-ba6a-4c62-864a-a0b154ff6a55

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (F K : Type*) [Field F] [Field K]
    (f : Polynomial F →+* K) (hf : Function.Injective f) :
    (IsFractionRing.lift (K := FractionRing (Polynomial F)) hf).comp
      (algebraMap (Polynomial F) (FractionRing (Polynomial F))) = f := by
  apply RingHom.ext
  intro P
  exact IsFractionRing.lift_algebraMap hf P
end QEC.Coding.TannerLiftedProduct
