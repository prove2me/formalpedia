-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.chartIndexAt_source
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:25:46.772444+00:00
-- url     : https://prove2.me/submissions/551d426a-f3d0-4eb5-89b9-01bd7584e288

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
import Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_fsPot_U_ite
import Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_chart_chartIndexAt_infty
import Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_chart_chartIndexAt_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
open ReciprocityTheory.AnForm.M.CompatibleChartOperations
namespace ReciprocityTheory.AnForm.M.CompatibleChartOperations
theorem _root_.solution (a : OnePoint ℂ) : (p1.chart (chartIndexAt a)).source = fsPot.U a := by
  rw [fsPot_U_ite]
  by_cases ha : a = ∞
  · rw [chart_chartIndexAt_infty ha, if_pos ha]
  · rw [chart_chartIndexAt_fin ha, if_neg ha]
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
