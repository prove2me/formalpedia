-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.support_coker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:46.662696+00:00
-- url     : https://prove2.me/submissions/09eef799-bf8f-4fae-a234-d7aa00ab4c0a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_range_lsmul_eq

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
theorem _root_.solution (N : Type v) [AddCommGroup N] [Module A N] [Module.Finite A N] (x : A) :
    support A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) = support A N ∩ zeroLocus {x} := by
  rw [← Module.support_quotSMulTop]
  exact (Submodule.quotEquivOfEq _ _ (range_lsmul_eq N x)).support_eq
end ReciprocityTheory.ChartRestriction.G.AI
