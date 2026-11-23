-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:11.088098+00:00
-- url     : https://prove2.me/submissions/e7f26337-f81b-4bc3-ac1f-65cfb8bef6c2

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPrecompleteFiniteModule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion

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
namespace ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
theorem _root_.solution : FaithfulSMul R L :=
  (faithfulSMul_iff_algebraMap_injective R L).2 (by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K))
end ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
