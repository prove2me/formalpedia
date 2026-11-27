-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_M_CompatibleChartOperations_fsPot___eq_f40018ae65da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:13:30.140573+00:00
-- url     : https://prove2.me/submissions/b0e6e2c6-2360-42d9-a6ea-e931f093394e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_CompatibleChartOperations_fsPot___ite_c35675c87367
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
theorem _root_.solution (a p : OnePoint ℂ) : fsPot.φ a p = Real.log (nrm2 (homogeneousLift a p)) := by
  rw [fsPot_φ_ite]
  unfold nrm2 homogeneousLift
  split_ifs <;> simp only [norm_one, one_pow] <;> rw [Real.log_sqrt (by positivity)] <;> ring_nf
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
