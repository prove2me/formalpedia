-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:16.876802+00:00
-- url     : https://prove2.me/submissions/674c8464-ad3a-4952-890b-9f4984ed01c3

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
  (L : Type*) [Field L] [Algebra R L] [FaithfulSMul R L] [Module.Finite R (integralClosure R L)]
namespace ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
theorem _root_.solution : Function.Injective (algebraMap R (integralClosure R L)) := by
  intro x y h
  apply FaithfulSMul.algebraMap_injective R L
  exact congrArg Subtype.val h
end ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
