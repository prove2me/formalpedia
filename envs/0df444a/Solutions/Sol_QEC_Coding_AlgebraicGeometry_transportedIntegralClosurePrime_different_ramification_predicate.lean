-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.transportedIntegralClosurePrime_different_ramification_predicate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:41:35.889206+00:00
-- url     : https://prove2.me/submissions/59b34949-7092-4569-b6c0-d91dda92bccb

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_LocalizedPrime
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_localizedIntegralClosurePrime_ramificationIdx_and_multiplicity_eq
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
private theorem scalarTower_of_commuting_square
    (R S T U : Type*)
    [CommSemiring R] [CommSemiring S] [CommSemiring T] [Semiring U]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [Algebra T U] [Algebra S U] [Algebra R U]
    [IsScalarTower R S T] [IsScalarTower S T U]
    [IsScalarTower R T U] :
    IsScalarTower R S U :=
  IsScalarTower.of_algebraMap_eq fun x => by
    calc
      algebraMap R U x = algebraMap T U (algebraMap R T x) :=
        IsScalarTower.algebraMap_apply R T U x
      _ = algebraMap T U (algebraMap S T (algebraMap R S x)) := by
        rw [IsScalarTower.algebraMap_apply R S T x]
      _ = algebraMap S U (algebraMap R S x) :=
        (IsScalarTower.algebraMap_apply S T U (algebraMap R S x)).symm
private theorem transportedSubring_isLocalization
    (B K : Type*) [CommRing B] [_root_.Field K]
    (M : Submonoid B) (S T : ValuationSubring K) [Algebra B S]
    [IsLocalization M S] (h : S = T) :
    letI : Algebra B T := transportedSubringAlgebra B K S T h
    IsLocalization M T := by
  exact (IsLocalization.isLocalization_iff_of_ringEquiv M
    (valuationSubringRingEquivOfEq S T h)).mp inferInstance
end
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {k : Type*} [_root_.Field k] [Finite k]
    (A B K L : Type*)
    [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B]
    [Algebra k K]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L]
    [IsScalarTower P.valuationRing K L]
    [FaithfulSMul P.valuationRing L]
    [IsDedekindDomain (integralClosure B L)]
    [Module.IsTorsionFree B (integralClosure B L)]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [Module.IsTorsionFree P.valuationRing
      (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (hvaluationRing : H.valuationSubringAtPrime K = P.valuationRing)
    (J : Ideal (integralClosure B L))
    [J.IsPrime] [J.LiesOver H.asIdeal]
    (Φ : ℕ → ℕ → Prop)
    (hlocal : ∀ R : Ideal (integralClosure P.valuationRing L),
      R.IsPrime →
      R.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) →
      Φ (multiplicity R
          (differentIdeal P.valuationRing
            (integralClosure P.valuationRing L)))
        ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' R)) :
    Φ (multiplicity J (differentIdeal B (integralClosure B L)))
      (H.asIdeal.ramificationIdx' J) := by
  letI : Algebra B P.valuationRing :=
    transportedSubringAlgebra B K
      (H.valuationSubringAtPrime K) P.valuationRing hvaluationRing
  letI : IsLocalization H.asIdeal.primeCompl P.valuationRing :=
    transportedSubring_isLocalization B K H.asIdeal.primeCompl
      (H.valuationSubringAtPrime K) P.valuationRing hvaluationRing
  let e : H.valuationSubringAtPrime K ≃+* P.valuationRing :=
    valuationSubringRingEquivOfEq _ _ hvaluationRing
  letI : IsScalarTower B P.valuationRing K :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap B K x = algebraMap P.valuationRing K
        (e (algebraMap B (H.valuationSubringAtPrime K) x))
      calc
        algebraMap B K x = algebraMap (H.valuationSubringAtPrime K) K
            (algebraMap B (H.valuationSubringAtPrime K) x) :=
          IsScalarTower.algebraMap_apply B (H.valuationSubringAtPrime K) K x
        _ = _ := rfl
  letI : IsScalarTower B P.valuationRing L :=
    scalarTower_of_commuting_square B P.valuationRing K L
  letI : Module.IsTorsionFree B P.valuationRing :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (IsLocalization.injective (S := P.valuationRing)
        H.asIdeal.primeCompl_le_nonZeroDivisors)
  letI : Module.IsTorsionFree P.valuationRing L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective P.valuationRing L)
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  let R : Ideal (integralClosure P.valuationRing L) :=
    Ideal.map (localizedIntegralClosureMap B P.valuationRing L) J
  have htransported :=
    localizedIntegralClosurePrime_ramificationIdx_and_multiplicity_eq
      A B P.valuationRing K L H.asIdeal H.ne_bot J
  dsimp only at htransported
  have hRprime : R.IsPrime := by
    simpa only [R] using htransported.1
  have hRlies :
      R.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) := by
    simpa only [R] using htransported.2.1
  have hramification :
      (IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' R =
        H.asIdeal.ramificationIdx' J := by
    simpa only [R] using htransported.2.2.1
  have hmultiplicity :
      multiplicity R
          (differentIdeal P.valuationRing
            (integralClosure P.valuationRing L)) =
        multiplicity J (differentIdeal B (integralClosure B L)) := by
    simpa only [R] using htransported.2.2.2
  rw [← hmultiplicity, ← hramification]
  exact hlocal R hRprime hRlies
end QEC.Coding.AlgebraicGeometry
