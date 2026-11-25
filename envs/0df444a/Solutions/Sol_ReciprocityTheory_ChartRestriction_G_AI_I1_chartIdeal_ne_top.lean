-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:02:45.094801+00:00
-- url     : https://prove2.me/submissions/09861acf-767b-41e1-8f22-bdf2a98eedc8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartRho_chartIdeal

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
theorem _root_.solution (hW : IsMultiHomogIdeal W) {j : ∀ k, ι k} (hj : IsChart W j) :
    chartIdeal W j ≠ ⊤ := by
  intro h
  have h1 := chartRho_chartIdeal hW hj ((Ideal.eq_top_iff_one _).mp h)
  rw [map_one] at h1
  exact one_ne_zero h1
end ReciprocityTheory.ChartRestriction.G.AI.I1
