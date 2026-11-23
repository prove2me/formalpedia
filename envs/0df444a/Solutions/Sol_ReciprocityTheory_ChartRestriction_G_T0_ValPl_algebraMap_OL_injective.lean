-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValPl.algebraMap_OL_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:04.256434+00:00
-- url     : https://prove2.me/submissions/17760ade-6bf1-40e9-b6d3-1b2cfc01c5de

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValPl
open IsDedekindDomain WithZero IsLocalRing
variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
include F
namespace ReciprocityTheory.ChartRestriction.G.T0.ValPl
theorem _root_.solution : Function.Injective (algebraMap O L) := by
  rw [IsScalarTower.algebraMap_eq O F L]
  first
  | exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  | (rw [RingHom.coe_comp]; exact (algebraMap F L).injective.comp (IsFractionRing.injective O F))
end ReciprocityTheory.ChartRestriction.G.T0.ValPl
