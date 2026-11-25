-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_M_CompatibleChartOperations_fsPot___ite_c35675c87367
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:32:16.046259+00:00
-- url     : https://prove2.me/submissions/00336a28-ac56-426e-9771-d311841ad63c

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
open scoped Classical
namespace ReciprocityTheory.AnForm.M.CompatibleChartOperations
theorem _root_.solution (a p : OnePoint ℂ) : fsPot.φ a p = if a = ∞ then (1 / 2) * Real.log (1 + ‖crd1 p‖ ^ 2)
    else (1 / 2) * Real.log (1 + ‖crd0 p‖ ^ 2) := rfl
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
