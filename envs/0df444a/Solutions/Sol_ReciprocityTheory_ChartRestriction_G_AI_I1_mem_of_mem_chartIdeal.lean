-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.mem_of_mem_chartIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:03:35.017937+00:00
-- url     : https://prove2.me/submissions/dafb2cc5-7a0f-4b3d-a830-5685fdc9fb52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartRho_chartIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartRho_form

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
theorem _root_.solution [DecidableEq K] (hW : IsMultiHomogIdeal W) {j : ∀ k, ι k}
    (hj : IsChart W j) {e : K → ℕ} {a : MRingOver F ι}
    (ha : a ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) e) (haW : a ∈ chartIdeal W j) : a ∈ W := chartRho_form hj ha (chartRho_chartIdeal hW hj haW)
end ReciprocityTheory.ChartRestriction.G.AI.I1
