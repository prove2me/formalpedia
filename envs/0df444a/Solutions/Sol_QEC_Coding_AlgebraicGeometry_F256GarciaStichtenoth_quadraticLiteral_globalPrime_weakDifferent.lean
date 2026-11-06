-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_globalPrime_weakDifferent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:03:39.035412+00:00
-- url     : https://prove2.me/submissions/3beb1856-09ec-4356-afc6-97889a05ef28

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_allPrime_weakDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_transportedIntegralClosurePrime_weak_formula


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
    (P : GlobalPlace F256 K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [FaithfulSMul P.valuationRing L]
    [IsDedekindDomain (integralClosure B L)]
    [Module.IsTorsionFree B (integralClosure B L)]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (hvaluationRing : H.valuationSubringAtPrime K = P.valuationRing)
    (J : Ideal (integralClosure B L)) [J.IsPrime] [J.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : P.order a = -1 ∨ 0 ≤ P.order a) :
    multiplicity J (differentIdeal B (integralClosure B L)) =
      2 * (H.asIdeal.ramificationIdx' J - 1) := by
  apply transportedIntegralClosurePrime_weak_formula A B K L P H hvaluationRing J
  intro R hRprime hRlies
  let O := P.valuationRing
  let C := integralClosure O L
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree O L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective O L)
  letI : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
  letI : R.IsPrime := hRprime
  letI : R.LiesOver (IsLocalRing.maximalIdeal O) := hRlies
  have hRne : R ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field O) R
  let HR : IsDedekindDomain.HeightOneSpectrum C := ⟨R, hRprime, hRne⟩
  exact quadraticLiteral_allPrime_weakDifferent P HR a y hy hdegree hgen ha
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
