-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.locallyIntegrable_real_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:27.949748+00:00
-- url     : https://prove2.me/submissions/5439f905-36c8-47c2-b6ed-7165461b3594

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt

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
theorem _root_.solution : LocallyIntegrable Real.log volume := by
  intro x
  refine ⟨Set.Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
    intervalIntegral.intervalIntegrable_log'
end ReciprocityTheory.AnForm.A
