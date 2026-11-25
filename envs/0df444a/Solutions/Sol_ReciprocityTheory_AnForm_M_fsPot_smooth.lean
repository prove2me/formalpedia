-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.fsPot_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:01.747364+00:00
-- url     : https://prove2.me/submissions/feeb84a3-bd7d-4000-a66d-b4d674a5841b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_chart
import Theorems.Thm_ReciprocityTheory_AnForm_M_contDiffOn_fubiniStudyProfileInv_normSqFirst
import Theorems.Thm_ReciprocityTheory_AnForm_M_contDiff_fubiniStudyProfile_normSqFirst


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
theorem _root_.solution (x : OnePoint ℂ) : p1.SmoothOn (fsPot.U x) (fsPot.φ x) := by
  intro j
  rcases fsPot_chart x j with h | ⟨h, hne⟩
  · rw [h]
    exact contDiff_fubiniStudyProfile_normSqFirst.contDiffOn
  · rw [h]
    exact contDiffOn_fubiniStudyProfileInv_normSqFirst.mono fun w hw => hne w hw
end ReciprocityTheory.AnForm.M
