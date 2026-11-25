-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.mIntCongrNull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:25:56.380715+00:00
-- url     : https://prove2.me/submissions/99978c29-bdda-4ed6-be38-ff3b2319a5e9

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Theorems.Thm_ReciprocityTheory_AnForm_M_integralWith_congr_null

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
theorem _root_.solution : MIntCongrNullStatement := by
  unfold MIntCongrNullStatement
  intro e X _ A Φ S hS hint g g' hg
  unfold mInt
  split_ifs with h
  · exact integralWith_congr_null A h.some Φ hS hint hg
  · rfl
end ReciprocityTheory.AnForm.M
