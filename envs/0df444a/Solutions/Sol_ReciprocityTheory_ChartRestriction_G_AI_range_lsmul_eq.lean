-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.range_lsmul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:05.936979+00:00
-- url     : https://prove2.me/submissions/17cb5032-5514-4d14-ad16-5037530f11eb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (N : Type v) [AddCommGroup N] [Module A N] (x : A) :
    LinearMap.range (LinearMap.lsmul A N x) = x • (⊤ : Submodule A N) := by
  ext m
  simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_top, true_and]
end ReciprocityTheory.ChartRestriction.G.AI
