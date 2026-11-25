-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.chart_chartIndexAt_infty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:30:18.131439+00:00
-- url     : https://prove2.me/submissions/1762eab8-9666-47eb-bd87-c01df3874510

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd

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
theorem _root_.solution {a : OnePoint ℂ} (ha : a = ∞) : p1.chart (chartIndexAt a) = projectiveLineChartAtInfinity := by
  rw [chartIndexAt, if_pos ha]
  rfl
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
