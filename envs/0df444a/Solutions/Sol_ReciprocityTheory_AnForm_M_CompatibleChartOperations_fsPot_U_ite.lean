-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.fsPot_U_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:29:02.378006+00:00
-- url     : https://prove2.me/submissions/7173c489-1012-4af2-8b74-08447774cabf

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
theorem _root_.solution (a : OnePoint ℂ) :
    fsPot.U a = if a = ∞ then projectiveLineChartAtInfinity.source else projectiveLineChartAtZero.source := rfl
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
