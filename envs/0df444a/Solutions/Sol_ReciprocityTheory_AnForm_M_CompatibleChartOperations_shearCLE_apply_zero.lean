-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.shearCLE_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:23:19.545635+00:00
-- url     : https://prove2.me/submissions/ac7595c1-45ea-44b5-ab23-ff4aec085ed4

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
theorem _root_.solution (v : Fin 2 → ℂ) : shearCLE v 0 = v 0 - v 1 := rfl
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
