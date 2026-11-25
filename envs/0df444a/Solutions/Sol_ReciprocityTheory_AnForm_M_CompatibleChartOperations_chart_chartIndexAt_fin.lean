-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.chart_chartIndexAt_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:30:14.302398+00:00
-- url     : https://prove2.me/submissions/adba7828-4f20-49b9-b3f2-475c8e24ee8b

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
theorem _root_.solution {a : OnePoint ℂ} (ha : a ≠ ∞) : p1.chart (chartIndexAt a) = projectiveLineChartAtZero := by
  rw [chartIndexAt, if_neg ha]
  rfl
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
