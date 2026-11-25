-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.analyticNull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:12:47.432531+00:00
-- url     : https://prove2.me/submissions/3cb5a5f0-3fb9-49dc-a8ea-10a161706b47

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Theorems.Thm_ReciprocityTheory_AnForm_M_analyticSubset_chart_local
import Theorems.Thm_ReciprocityTheory_AnForm_volume_eq_zero_of_locally_in_analytic_zero_set


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : AnalyticNullStatement := by
  intro e X _ A S hS hint j
  exact ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set _
    (fun z hz => analyticSubset_chart_local A hS hint j hz)
end ReciprocityTheory.AnForm.M
