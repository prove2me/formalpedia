-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.sec_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:14:50.377743+00:00
-- url     : https://prove2.me/submissions/9715043b-5952-400f-8468-7eb4b3d3e05d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WeightIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenThick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenLevel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_exists_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_toW_mul_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_toW_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) [Flat p]
    {M : LB Y} (s : LB.Sec M) {a : R} (ha : a ≠ 0) {J : Ideal R} (hJ : J ≤ Ideal.span {a})
    (h0 : ∀ j, (pullback.fst p (tq J)).app _ (s.f j) = 0) :
    ∃ g : LB.Sec M, ∀ j, s.f j = toW p _ a * g.f j := by
  choose g hg using fun j => exists_div p ha hJ (M.U j) (s.f j) (h0 j)
  refine ⟨⟨g, fun i j => ?_⟩, hg⟩
  apply sub_eq_zero.1
  apply toW_mul_eq_zero p _ ha
  have c := s.compat i j
  rw [hg i, hg j, map_mul, map_mul, toW_res, toW_res] at c
  rw [mul_sub, sub_eq_zero, c]
  ring
end ReciprocityTheory.ChartRestriction.G.DVR.TG
