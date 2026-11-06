-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_heightOnePrime_normalizing_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:21:04.670039+00:00
-- url     : https://prove2.me/submissions/8412b333-11ff-46ac-8394-5bea84b81db8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticNormalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalNormalization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_allPrime_normalizing_correction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_transportedIntegralClosurePrime_order_predicate


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
    [IsFractionRing (integralClosure B L) L]
    [Module.IsTorsionFree B (integralClosure B L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    [Finite (heightOnePlace (k := F256) (K := K) H).residueField]
    (J : IsDedekindDomain.HeightOneSpectrum (integralClosure B L))
    [J.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order a)
    (b : K)
    (hb : (heightOnePlace (k := F256) (K := K) H).order b = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order b) :
    ∃ c : L,
      (c = 0 ∨ (heightOnePlace (k := F256) (K := L) J).order c = -1) ∧
      ((heightOnePlace (k := F256) (K := L) J).order (algebraMap K L b + c ^ 2 + c) = -1 ∨
        0 ≤ (heightOnePlace (k := F256) (K := L) J).order (algebraMap K L b + c ^ 2 + c)) := by
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
  apply transportedIntegralClosurePrime_order_predicate A B K L P H
    (heightOnePlace_valuationRing H) J
    (fun ord => ∃ c : L, (c = 0 ∨ ord c = -1) ∧
      (ord (algebraMap K L b + c ^ 2 + c) = -1 ∨
        0 ≤ ord (algebraMap K L b + c ^ 2 + c)))
  intro R hRlies
  letI : R.asIdeal.LiesOver (IsLocalRing.maximalIdeal O) := hRlies
  exact quadraticLiteral_allPrime_normalizing_correction P R a y hy hdegree hgen ha b hb
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
