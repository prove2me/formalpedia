-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_of_charZero_6b5f227e7c28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:10:26.512121+00:00
-- url     : https://prove2.me/submissions/3ae5f803-3bf2-4341-af36-9722348d7cb6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_fractionRing_of_charZero_ff051fc57786

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped nonZeroDivisors
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution
    (A : Type*) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] :
    Module.Finite A (integralClosure A L) := by
  have : Module.Finite A (integralClosure A K) :=
    finite_integralClosure_fractionRing_of_charZero A K
  set A' := integralClosure A K
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  have : IsNoetherianRing A' := IsNoetherianRing.of_finite A A'
  have : IsIntegrallyClosed A' := integralClosure.isIntegrallyClosedOfFiniteExtension K (L := K)
  have : IsFractionRing A' K := integralClosure.isFractionRing_of_finite_extension K K
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  have : Algebra.IsSeparable K L := Algebra.IsSeparable.of_integral K L
  have : IsScalarTower A' K L := inferInstance
  have : IsScalarTower A A' L := inferInstance
  have : Module.Finite A' (integralClosure A' L) :=
    IsIntegralClosure.finite A' K L (integralClosure A' L)
  have : Module.Finite A (integralClosure A' L) := Module.Finite.trans A' _
  have hle : (integralClosure A L).toSubmodule ≤
      (integralClosure A' L).toSubmodule.restrictScalars A := fun y hy => hy.tower_top
  have : IsNoetherian A ((integralClosure A' L).toSubmodule.restrictScalars A) :=
    isNoetherian_of_isNoetherianRing_of_finite A (integralClosure A' L)
  have : IsNoetherian A (integralClosure A L).toSubmodule := isNoetherian_of_le hle
  exact Module.IsNoetherian.finite A (integralClosure A L).toSubmodule
end GroundTheory.Heights₂.Heights.Model
