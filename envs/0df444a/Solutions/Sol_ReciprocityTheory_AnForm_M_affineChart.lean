-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.affineChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:25:20.252581+00:00
-- url     : https://prove2.me/submissions/456043f1-b6a1-4ee2-a7cb-1b07c57994ae

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Theorems.Thm_ReciprocityTheory_AnForm_M_pa_compat_chart
import Theorems.Thm_ReciprocityTheory_AnForm_M_pa_compat_aff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : AffineChartStatement := by
  intro e X _ A j a b ha
  exact ⟨(A.chart j).transHomeomorph (pa_aff a ha b), pa_compat_aff A _ (pa_compat_chart A j) a ha b, rfl,
    fun x _ => rfl⟩
end ReciprocityTheory.AnForm.M
