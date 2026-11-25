-- Prove2me | solution 1 for UpperTheory.integralClosure_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:08:57.223864+00:00
-- url     : https://prove2.me/submissions/5eed41d0-1bb6-4bca-9f70-858e92a531e8

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FiniteOfFiniteOverNormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UpperTheory
open nonZeroDivisors
private theorem finite_of_finite_over_normal (P A K : Type*) [CommRing P] [IsDomain P]
    [CharZero P] [IsIntegrallyClosed P] [IsNoetherianRing P] [CommRing A] [IsDomain A]
    [Algebra P A] [FaithfulSMul P A] [Module.Finite P A] [Field K] [Algebra A K]
    [IsFractionRing A K] : Module.Finite A (integralClosure A K) := by
  letI : Algebra P K := ((algebraMap A K).comp (algebraMap P A)).toAlgebra
  haveI : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr
    ((IsFractionRing.injective A K).comp (FaithfulSMul.algebraMap_injective P A))
  letI : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K
  haveI : IsScalarTower P (FractionRing P) K := FractionRing.isScalarTower_liftAlgebra P K
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A P⁰) K := inferInstance
  haveI : FiniteDimensional (FractionRing P) K := Module.Finite.of_isLocalization P A P⁰
  haveI : CharZero (FractionRing P) := IsFractionRing.charZero P
  haveI : Algebra.IsSeparable (FractionRing P) K := inferInstance
  haveI : IsIntegralClosure (integralClosure A K) P K :=
    ⟨Subtype.val_injective, fun {x} =>
      ⟨fun hx => ⟨⟨x, hx.tower_top⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ isIntegral_trans _ y.2⟩⟩
  haveI : Module.Finite P (integralClosure A K) :=
    IsIntegralClosure.finite P (FractionRing P) K (integralClosure A K)
  exact Module.Finite.of_restrictScalars_finite P A (integralClosure A K)
end UpperTheory
end

set_option autoImplicit false
open UpperTheory
open nonZeroDivisors
namespace UpperTheory
theorem _root_.solution (k A K : Type*) [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K] :
    Module.Finite A (integralClosure A K) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact finite_of_finite_over_normal (MvPolynomial (Fin s) k) A K
end UpperTheory
