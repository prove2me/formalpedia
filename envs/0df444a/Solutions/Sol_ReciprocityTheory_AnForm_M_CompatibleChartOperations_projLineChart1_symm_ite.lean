-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.projLineChart1_symm_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:23:08.686242+00:00
-- url     : https://prove2.me/submissions/d32cb2da-3f26-428d-b1bd-fa469ce52e7d

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
theorem _root_.solution (t : Fin 1 → ℂ) :
    projectiveLineChartAtInfinity.symm t = if t 0 = 0 then ∞ else (((t 0)⁻¹ : ℂ) : OnePoint ℂ) := rfl
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
