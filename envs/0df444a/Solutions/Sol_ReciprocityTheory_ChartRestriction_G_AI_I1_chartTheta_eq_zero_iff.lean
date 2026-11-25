-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.chartTheta_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:35:08.21287+00:00
-- url     : https://prove2.me/submissions/5aeb1298-ae21-4040-ad69-1d87ac773255

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartTheta_apply

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
variable {W : Ideal (MRingOver F ι)} [hWp : W.IsPrime]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution {g : MRingOver F ι} : chartTheta W g = 0 ↔ g ∈ W := by
  rw [chartTheta_apply, map_eq_zero_iff _
    (IsFractionRing.injective (MRingOver F ι ⧸ W) (FractionRing (MRingOver F ι ⧸ W))),
    Ideal.Quotient.eq_zero_iff_mem]
end ReciprocityTheory.ChartRestriction.G.AI.I1
