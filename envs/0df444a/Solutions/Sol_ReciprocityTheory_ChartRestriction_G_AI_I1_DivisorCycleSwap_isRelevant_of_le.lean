-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.isRelevant_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:58.285659+00:00
-- url     : https://prove2.me/submissions/5a90b912-6597-4120-a0c4-6db53165569d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
open SwapLoc
open ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
namespace ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
theorem _root_.solution {Y Z : Ideal (MRingOver F ι)} (hZ : IsRelevant Z) (hY : Y ≤ Z) :
    IsRelevant Y := fun k => by
  obtain ⟨i, hi⟩ := hZ k
  exact ⟨i, fun h => hi (hY h)⟩
end ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
