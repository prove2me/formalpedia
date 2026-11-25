-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.logCoordLocInt_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:45.040807+00:00
-- url     : https://prove2.me/submissions/83f063f8-22ff-4be8-b91c-ab5fda2f3fdd

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Theorems.Thm_ReciprocityTheory_AnForm_A_locallyIntegrable_comp_eval_fin
import Theorems.Thm_ReciprocityTheory_AnForm_A_logNormLocIntC_thm

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
theorem _root_.solution : LogCoordLocIntStatement := fun D i => locallyIntegrable_comp_eval_fin i logNormLocIntC_thm
end ReciprocityTheory.AnForm.A
