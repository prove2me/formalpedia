-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_heightOnePrime_weakDifferent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:05:37.860354+00:00
-- url     : https://prove2.me/submissions/3d10edae-f388-4353-b572-ab0ed20b1d17

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_globalPrime_weakDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_valuationRing


set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (A B K L : Type*) [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra F256 K] [Algebra F256 L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    [IsDedekindDomain (integralClosure B L)]
    [Module.IsTorsionFree B (integralClosure B L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (J : Ideal (integralClosure B L)) [J.IsPrime] [J.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order a) :
    multiplicity J (differentIdeal B (integralClosure B L)) =
      2 * (H.asIdeal.ramificationIdx' J - 1) := by
  let P := heightOnePlace (k := F256) (K := K) H
  let O := P.valuationRing
  letI : Algebra O L := ((algebraMap K L).comp (algebraMap O K)).toAlgebra
  letI : IsScalarTower O K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree O L := Module.IsTorsionFree.trans_faithfulSMul O K L
  letI : FaithfulSMul O L := Module.isTorsionFree_iff_faithfulSMul.mp inferInstance
  letI : IsDedekindDomain (integralClosure O L) := integralClosure.isDedekindDomain O K L
  letI : Module.IsTorsionFree O (integralClosure O L) := IsIntegralClosure.isTorsionFree O L
  exact quadraticLiteral_globalPrime_weakDifferent A B K L P H
    (heightOnePlace_valuationRing H) J a y hy hdegree hgen ha
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
