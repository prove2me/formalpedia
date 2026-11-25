-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:33:28.283567+00:00
-- url     : https://prove2.me/submissions/69b059ed-8528-4175-ae97-53340cc9e4f8

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPrecompleteFiniteModule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_isLocalRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_faithful

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
open IsLocalRing Polynomial
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
include K
variable [Module.Finite R (integralClosure R L)]
namespace ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
theorem _root_.solution [IsAdicComplete (maximalIdeal R) R] :
    IsDiscreteValuationRing (integralClosure R L) := by
  have := cl_faithful R K L
  have : IsLocalRing (integralClosure R L) := cl_isLocalRing R L
  have : IsFractionRing (integralClosure R L) L := integralClosure.isFractionRing_of_finite_extension K L
  have : Algebra.IsIntegral R (integralClosure R L) := IsIntegralClosure.isIntegral_algebra R L
  have : IsNoetherianRing (integralClosure R L) :=
    isNoetherianRing_iff.mpr (isNoetherian_of_tower R inferInstance)
  have hD : IsDedekindDomain (integralClosure R L) :=
    { ‹IsNoetherianRing (integralClosure R L)›,
      Ring.DimensionLEOne.of_isIntegral R (integralClosure R L),
      (isIntegrallyClosed_iff L).mpr fun {x} hx =>
        ⟨IsIntegralClosure.mk' (integralClosure R L) x (isIntegral_trans (R := R) _ hx),
          IsIntegralClosure.algebraMap_mk' _ _ _⟩ with : IsDedekindDomain (integralClosure R L) }
  have hnf : ¬ IsField (integralClosure R L) := fun h =>
    (isField_iff_maximalIdeal_eq.not.mpr IsDiscreteValuationRing.not_a_field')
      (isField_of_isIntegral_of_isField (cl_inj R L) h)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure R L) hnf).out 0 2).mpr hD
end ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
