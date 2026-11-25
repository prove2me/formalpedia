-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.chartTheta_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:32.029813+00:00
-- url     : https://prove2.me/submissions/f5c85359-318e-4f5f-a78b-196164cc4a72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt

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
theorem _root_.solution (g : MRingOver F ι) :
    chartTheta W g = algebraMap (MRingOver F ι ⧸ W) (FractionRing (MRingOver F ι ⧸ W))
      (Ideal.Quotient.mk W g) := rfl
end ReciprocityTheory.ChartRestriction.G.AI.I1
