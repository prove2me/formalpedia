-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.pairDet_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:32:01.929927+00:00
-- url     : https://prove2.me/submissions/9be94534-ec8c-40ac-8825-4a50130979ff

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
open ReciprocityTheory.AnForm.M.CompatibleChartOperations
namespace ReciprocityTheory.AnForm.M.CompatibleChartOperations
theorem _root_.solution (c d : ℂ) (u v : ℂ × ℂ) : det2 (c • u) (d • v) = c * d * det2 u v := by
  simp only [det2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
