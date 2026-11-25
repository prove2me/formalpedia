-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.contDiff_fubiniStudyProfile_normSqFirst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:03.622814+00:00
-- url     : https://prove2.me/submissions/a18618d6-7b57-4994-8541-e676751ed671

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Theorems.Thm_ReciprocityTheory_AnForm_M_contDiff_fsQ

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
theorem _root_.solution : ContDiff ℝ (⊤ : ℕ∞) (fun w => fubiniStudyProfile (fsQ w)) := by
  unfold fubiniStudyProfile
  refine contDiff_const.mul ((contDiff_const.add contDiff_fsQ).log fun w => ?_)
  have h0 : 0 ≤ fsQ w := by unfold fsQ; positivity
  exact ne_of_gt (by linarith)
end ReciprocityTheory.AnForm.M
