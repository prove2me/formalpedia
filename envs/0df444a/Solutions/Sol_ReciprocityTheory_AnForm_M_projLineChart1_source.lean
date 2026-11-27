-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projLineChart1_source
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:22:29.944056+00:00
-- url     : https://prove2.me/submissions/682e6fdb-3d42-4ffc-b6df-109f12b4e22f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : projectiveLineChartAtInfinity.source = {x | x ≠ ((0 : ℂ) : OnePoint ℂ)} := rfl
end ReciprocityTheory.AnForm.M
