-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.logMonoTestInt_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:26:01.776429+00:00
-- url     : https://prove2.me/submissions/c8101c89-1647-47d4-a854-2654ed0f1f70

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Theorems.Thm_ReciprocityTheory_AnForm_A_logMonoLocInt_thm

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
theorem _root_.solution : LogMonoTestIntStatement := by
  intro D m f hf hfs
  exact (logMonoLocInt_thm D m).integrable_smul_left_of_hasCompactSupport hf hfs
end ReciprocityTheory.AnForm.A
