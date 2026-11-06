-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.localizedIntegralClosurePrime_ramificationIdx_and_multiplicity_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:39:16.769209+00:00
-- url     : https://prove2.me/submissions/8ca6f46e-d9c2-41b3-a8c6-ad8a59e94f8c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Localization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalIntegralClosureFree
import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.Localization.Integral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_LocalizedPrime
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_differentIdeal_multiplicity_eq_of_isLocalization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_integralClosure_moduleFree_over_integralLocalBase


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (A B Bm K L : Type*)
    [CommRing A] [CommRing B] [CommRing Bm]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A]
    [IsDomain Bm] [IsLocalRing Bm]
    [IsDedekindDomain B] [IsDedekindDomain Bm]
    [Algebra A B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B]
    [Algebra B Bm] [Module.IsTorsionFree B Bm]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra Bm K] [IsScalarTower B Bm K]
    [Algebra Bm L] [IsScalarTower B Bm L]
    [IsScalarTower Bm K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L] [Module.IsTorsionFree Bm L]
    (p : Ideal B) [p.IsPrime] (hp : p ≠ ⊥)
    [IsLocalization p.primeCompl Bm]
    (J : Ideal (integralClosure B L))
    [J.IsPrime] [J.LiesOver p] :
    letI : IsFractionRing Bm K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
        p.primeCompl Bm K
    letI : IsScalarTower B (integralClosure B L) L :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Bm (integralClosure Bm L) L :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Module.IsTorsionFree B (integralClosure B L) :=
      IsIntegralClosure.isTorsionFree B L
    letI : Module.IsTorsionFree Bm (integralClosure Bm L) :=
      IsIntegralClosure.isTorsionFree Bm L
    letI : Module.Finite B (integralClosure B L) :=
      IsIntegralClosure.finite B K L (integralClosure B L)
    letI : Module.Finite Bm (integralClosure Bm L) :=
      IsIntegralClosure.finite Bm K L (integralClosure Bm L)
    letI : IsDedekindDomain (integralClosure B L) :=
      integralClosure.isDedekindDomain B K L
    letI : IsDedekindDomain (integralClosure Bm L) :=
      integralClosure.isDedekindDomain Bm K L
    let R := Ideal.map (localizedIntegralClosureMap B Bm L) J
    R.IsPrime ∧
      R.LiesOver (IsLocalRing.maximalIdeal Bm) ∧
      (IsLocalRing.maximalIdeal Bm).ramificationIdx' R =
        p.ramificationIdx' J ∧
      multiplicity R (differentIdeal Bm (integralClosure Bm L)) =
        multiplicity J (differentIdeal B (integralClosure B L)) := by
  letI : IsFractionRing Bm K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      p.primeCompl Bm K
  let C := integralClosure B L
  let Cm := integralClosure Bm L
  let φ : C →+* Cm := localizedIntegralClosureMap B Bm L
  letI : Algebra C Cm := φ.toAlgebra
  letI hBCm : IsScalarTower B C Cm :=
    IsScalarTower.of_algebraMap_eq fun x => by
      apply Subtype.ext
      rw [Subalgebra.coe_algebraMap]
      change algebraMap B L x = ((φ (algebraMap B C x) : Cm) : L)
      rfl
  letI : IsScalarTower B Bm Cm :=
    IsScalarTower.of_algebraMap_eq fun x => by
      apply Subtype.ext
      rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]
      exact IsScalarTower.algebraMap_apply B Bm L x
  letI : IsScalarTower Bm Cm L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower C Cm L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower B C L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing C L :=
    integralClosure.isFractionRing_of_finite_extension K L
  letI : IsFractionRing Cm L :=
    integralClosure.isFractionRing_of_finite_extension K L
  letI : IsDedekindDomain C := integralClosure.isDedekindDomain B K L
  letI : IsDedekindDomain Cm := integralClosure.isDedekindDomain Bm K L
  letI : Module.IsTorsionFree B C :=
    IsIntegralClosure.isTorsionFree B L
  letI : Module.IsTorsionFree Bm Cm :=
    IsIntegralClosure.isTorsionFree Bm L
  letI : Module.Finite B C := IsIntegralClosure.finite B K L C
  letI : Module.Finite Bm Cm := IsIntegralClosure.finite Bm K L Cm
  letI : Module.Free B C :=
    integralClosure_moduleFree_over_integralLocalBase A B K L C
  have hJne : J ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp J
  letI : J.IsMaximal := (inferInstance : J.IsPrime).isMaximal hJne
  let M := p.primeCompl
  letI : IsLocalization (Algebra.algebraMapSubmonoid L M) L := by
    apply IsLocalization.of_le_isUnit
    rintro _ ⟨m, hm, rfl⟩
    apply isUnit_iff_ne_zero.mpr
    exact (map_ne_zero_iff _
      (FaithfulSMul.algebraMap_injective B L)).mpr
      (nonZeroDivisors.ne_zero
        (p.primeCompl_le_nonZeroDivisors hm))
  letI : IsLocalization (Algebra.algebraMapSubmonoid C M) Cm :=
    IsLocalization.integralClosure (R := B) (S := L) M
      (Rf := Bm) (Sf := L)
  let m : Ideal Bm := IsLocalRing.maximalIdeal Bm
  let R : Ideal Cm := Ideal.map φ J
  letI : R.IsPrime := by
    dsimp only [R]
    exact IsLocalization.AtPrime.isPrime_map_of_liesOver C p Cm J
  letI : R.LiesOver m := by
    dsimp only [R, m]
    exact IsLocalization.AtPrime.liesOver_map_of_liesOver p Bm Cm J
  have hCM :
      Algebra.algebraMapSubmonoid C M ≤ nonZeroDivisors C := by
    rintro _ ⟨x, hx, rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    exact (map_ne_zero_iff _
      (FaithfulSMul.algebraMap_injective B C)).mpr
        (nonZeroDivisors.ne_zero
          (p.primeCompl_le_nonZeroDivisors hx))
  letI : Module.IsTorsionFree C Cm :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (IsLocalization.injective (S := Cm) hCM)
  have hramification : m.ramificationIdx' R = p.ramificationIdx' J := by
    have hRne : R ≠ ⊥ := by
      change Ideal.map (algebraMap C Cm) J ≠ ⊥
      exact Ideal.map_ne_bot_of_ne_bot hJne
    have hmne : m ≠ ⊥ := by
      rw [Ideal.over_def R m]
      exact Ideal.under_ne_bot Bm hRne
    rw [Ideal.ramificationIdx'_eq_ramificationIdx m R hmne,
      Ideal.ramificationIdx'_eq_ramificationIdx p J hp]
    exact IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx
      p Bm Cm J
  have hdisjoint :
      Disjoint (Algebra.algebraMapSubmonoid C M : Set C) (J : Set C) := by
    exact Ideal.disjoint_primeCompl_of_liesOver J p
  have hmultiplicity :
      multiplicity R (differentIdeal Bm Cm) =
        multiplicity J (differentIdeal B C) := by
    exact differentIdeal_multiplicity_eq_of_isLocalization
      B C Bm Cm K L M J hdisjoint
  exact ⟨inferInstance, inferInstance, hramification, hmultiplicity⟩
end QEC.Coding.AlgebraicGeometry
