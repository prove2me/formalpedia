-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.transportedIntegralClosurePrime_weak_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:47:56.265134+00:00
-- url     : https://prove2.me/submissions/93d954e9-bd90-4667-9058-4b98821fcef0

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_LocalizedPrime
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_transportedIntegralClosurePrime_different_ramification_predicate

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {k : Type*} [_root_.Field k] [Finite k]
    (A B K L : Type*) [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra k K] [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.IsTorsionFree B L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [FaithfulSMul P.valuationRing L]
    [IsDedekindDomain (integralClosure B L)]
    [Module.IsTorsionFree B (integralClosure B L)]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (hvaluationRing : H.valuationSubringAtPrime K = P.valuationRing)
    (J : Ideal (integralClosure B L)) [J.IsPrime] [J.LiesOver H.asIdeal]
    (hlocal : ∀ R : Ideal (integralClosure P.valuationRing L),
      R.IsPrime → R.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) →
        multiplicity R (differentIdeal P.valuationRing (integralClosure P.valuationRing L)) =
          2 * ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' R - 1)) :
    multiplicity J (differentIdeal B (integralClosure B L)) =
      2 * (H.asIdeal.ramificationIdx' J - 1) :=
  transportedIntegralClosurePrime_different_ramification_predicate A B K L P H
    hvaluationRing J (fun d e => d = 2 * (e - 1)) hlocal
end QEC.Coding.AlgebraicGeometry
