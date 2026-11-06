-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_heightOnePrime_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:02:05.231657+00:00
-- url     : https://prove2.me/submissions/d7b8f595-2d1c-43c8-9709-c56d90ba5e47

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalRegular
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_different_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_ramificationIdx_eq_one_of_unit_different
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_transportedIntegralClosurePrime_different_ramification_predicate


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
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.IsTorsionFree B L]
    [IsDedekindDomain (integralClosure B L)]
    [Module.IsTorsionFree B (integralClosure B L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (J : Ideal (integralClosure B L)) [J.IsPrime] [J.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : 0 ≤ (heightOnePlace (k := F256) (K := K) H).order a) :
    H.asIdeal.ramificationIdx' J = 1 := by
  let P := heightOnePlace (k := F256) (K := K) H
  let O := P.valuationRing
  letI : Algebra O L := ((algebraMap K L).comp (algebraMap O K)).toAlgebra
  letI : IsScalarTower O K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree O L := Module.IsTorsionFree.trans_faithfulSMul O K L
  letI : FaithfulSMul O L := Module.isTorsionFree_iff_faithfulSMul.mp inferInstance
  letI : IsDedekindDomain (integralClosure O L) := integralClosure.isDedekindDomain O K L
  letI : IsFractionRing (integralClosure O L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  letI : Module.IsTorsionFree O (integralClosure O L) := IsIntegralClosure.isTorsionFree O L
  apply transportedIntegralClosurePrime_different_ramification_predicate A B K L P H
    (heightOnePlace_valuationRing H) J (fun _ e => e = 1)
  intro R hRprime hRlies
  letI : R.IsPrime := hRprime
  letI : R.LiesOver (IsLocalRing.maximalIdeal O) := hRlies
  let HR : IsDedekindDomain.HeightOneSpectrum (integralClosure O L) :=
    ⟨R, hRprime, Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field O) R⟩
  exact ramificationIdx_eq_one_of_unit_different
    (K := K) (L := L) (IsLocalRing.maximalIdeal O) HR
    (quadraticLiteral_different_eq_top P a ha y hy hdegree hgen)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
