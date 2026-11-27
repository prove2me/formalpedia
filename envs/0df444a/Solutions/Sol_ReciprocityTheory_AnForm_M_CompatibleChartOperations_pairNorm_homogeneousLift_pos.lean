-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.pairNorm_homogeneousLift_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:23:02.764733+00:00
-- url     : https://prove2.me/submissions/508eb6f3-1eee-4555-98ec-66f7315fb982

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
theorem _root_.solution (a p : OnePoint ℂ) : 0 < nrm2 (homogeneousLift a p) := by
  unfold nrm2 homogeneousLift
  apply Real.sqrt_pos.2
  split_ifs <;> simp only [norm_one, one_pow] <;> positivity
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
