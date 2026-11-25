-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.locallyIntegrable_norm_real_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:28.282127+00:00
-- url     : https://prove2.me/submissions/2602af56-6310-4ef8-ac4d-019bf6c663ea

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Theorems.Thm_ReciprocityTheory_AnForm_A_locallyIntegrable_real_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : LocallyIntegrable (fun x : ℝ => ‖Real.log x‖) volume := by
  intro x
  obtain ⟨s, hs, h⟩ := locallyIntegrable_real_log x
  exact ⟨s, hs, h.norm⟩
end ReciprocityTheory.AnForm.A
