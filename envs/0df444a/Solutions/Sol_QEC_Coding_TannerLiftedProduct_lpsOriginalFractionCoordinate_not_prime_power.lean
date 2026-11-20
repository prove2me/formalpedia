-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFractionCoordinate_not_prime_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:28:41.251263+00:00
-- url     : https://prove2.me/submissions/b6550e86-b2fc-4fa4-9a9a-da45421d8ec8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (F : Type*) [Field F] (p : ℕ) (hp : p.Prime)
    (u : FractionRing (Polynomial F)) :
    u^p ≠ algebraMap (Polynomial F) (FractionRing (Polynomial F)) Polynomial.X := by
  let e := RatFunc.toFractionRingRingEquiv (K := F)
  have hx : e.symm
      (algebraMap (Polynomial F) (FractionRing (Polynomial F)) Polynomial.X) =
      (RatFunc.X : RatFunc F) := by
    change RatFunc.ofFractionRing
      (algebraMap (Polynomial F) (FractionRing (Polynomial F)) Polynomial.X) = _
    rw [RatFunc.ofFractionRing_algebraMap,RatFunc.algebraMap_X]
  intro h
  have he := congrArg e.symm h
  rw [map_pow,hx] at he
  exact QEC.Coding.AlgebraicGeometry.ratFunc_coordinate_not_prime_power F p hp (e.symm u) he
end QEC.Coding.TannerLiftedProduct
