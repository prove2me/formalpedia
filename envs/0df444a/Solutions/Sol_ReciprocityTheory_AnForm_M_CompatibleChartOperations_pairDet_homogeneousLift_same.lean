-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.pairDet_homogeneousLift_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:22:54.850922+00:00
-- url     : https://prove2.me/submissions/b9f85773-6b68-469f-9ab6-d3ae60886d34

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
import Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_chart_chartIndexAt_infty
import Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_chart_chartIndexAt_fin
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
open ReciprocityTheory.AnForm.M.CompatibleChartOperations
open scoped Classical
namespace ReciprocityTheory.AnForm.M.CompatibleChartOperations
theorem _root_.solution (a p q : OnePoint ℂ) :
    det2 (homogeneousLift a p) (homogeneousLift a q) = (if a = ∞ then 1 else -1) * (chartCoordAt a p - chartCoordAt a q) := by
  by_cases ha : a = ∞
  · simp only [det2, homogeneousLift, chartCoordAt, if_pos ha, chart_chartIndexAt_infty ha]
    show crd1 p * 1 - 1 * crd1 q = 1 * (crd1 p - crd1 q)
    ring
  · simp only [det2, homogeneousLift, chartCoordAt, if_neg ha, chart_chartIndexAt_fin ha]
    show 1 * crd0 q - crd0 p * 1 = -1 * (crd0 p - crd0 q)
    ring
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
